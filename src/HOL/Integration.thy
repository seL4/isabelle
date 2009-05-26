(*  Author      : Jacques D. Fleuriot
    Copyright   : 2000  University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{*Theory of Integration*}

theory Integration
imports Deriv ATP_Linkup
begin

text{*We follow John Harrison in formalizing the Gauge integral.*}

definition
  --{*Partitions and tagged partitions etc.*}

  partition :: "[(real*real),nat => real] => bool" where
  [code del]: "partition = (%(a,b) D. D 0 = a &
                         (\<exists>N. (\<forall>n < N. D(n) < D(Suc n)) &
                              (\<forall>n \<ge> N. D(n) = b)))"

definition
  psize :: "(nat => real) => nat" where
  [code del]:"psize D = (SOME N. (\<forall>n < N. D(n) < D(Suc n)) &
                      (\<forall>n \<ge> N. D(n) = D(N)))"

definition
  tpart :: "[(real*real),((nat => real)*(nat =>real))] => bool" where
  [code del]:"tpart = (%(a,b) (D,p). partition(a,b) D &
                          (\<forall>n. D(n) \<le> p(n) & p(n) \<le> D(Suc n)))"

  --{*Gauges and gauge-fine divisions*}

definition
  gauge :: "[real set, real => real] => bool" where
  [code del]:"gauge E g = (\<forall>x\<in>E. 0 < g(x))"

definition
  fine :: "[real => real, ((nat => real)*(nat => real))] => bool" where
  [code del]:"fine = (%g (D,p). \<forall>n. n < (psize D) --> D(Suc n) - D(n) < g(p n))"

  --{*Riemann sum*}

definition
  rsum :: "[((nat=>real)*(nat=>real)),real=>real] => real" where
  "rsum = (%(D,p) f. \<Sum>n=0..<psize(D). f(p n) * (D(Suc n) - D(n)))"

  --{*Gauge integrability (definite)*}

definition
  Integral :: "[(real*real),real=>real,real] => bool" where
  [code del]: "Integral = (%(a,b) f k. \<forall>e > 0.
                               (\<exists>g. gauge {a..b} g &
                               (\<forall>D p. tpart(a,b) (D,p) & fine(g)(D,p) -->
                                         \<bar>rsum(D,p) f - k\<bar> < e)))"


lemma Integral_def2:
  "Integral = (%(a,b) f k. \<forall>e>0. (\<exists>g. gauge {a..b} g &
                               (\<forall>D p. tpart(a,b) (D,p) & fine(g)(D,p) -->
                                         \<bar>rsum(D,p) f - k\<bar> \<le> e)))"
unfolding Integral_def
apply (safe intro!: ext)
apply (fast intro: less_imp_le)
apply (drule_tac x="e/2" in spec)
apply force
done

lemma rsum_zero [simp]: "rsum (D,p) (\<lambda>x. 0) = 0"
unfolding rsum_def by simp

lemma rsum_left_distrib: "rsum (D,p) f * c = rsum (D,p) (\<lambda>x. f x * c)"
unfolding rsum_def
by (simp add: setsum_left_distrib setsum_right_distrib algebra_simps)

lemma rsum_right_distrib: "c * rsum (D,p) f = rsum (D,p) (\<lambda>x. c * f x)"
unfolding rsum_def
by (simp add: setsum_left_distrib setsum_right_distrib algebra_simps)

lemma rsum_add: "rsum (D, p) (%x. f x + g x) =  rsum (D, p) f + rsum(D, p) g"
by (simp add: rsum_def setsum_addf left_distrib)

lemma psize_unique:
  assumes 1: "\<forall>n < N. D(n) < D(Suc n)"
  assumes 2: "\<forall>n \<ge> N. D(n) = D(N)"
  shows "psize D = N"
unfolding psize_def
proof (rule some_equality)
  show "(\<forall>n<N. D(n) < D(Suc n)) \<and> (\<forall>n\<ge>N. D(n) = D(N))" using prems ..
next
  fix M assume "(\<forall>n<M. D(n) < D(Suc n)) \<and> (\<forall>n\<ge>M. D(n) = D(M))"
  hence 3: "\<forall>n<M. D(n) < D(Suc n)" and 4: "\<forall>n\<ge>M. D(n) = D(M)" by fast+
  show "M = N"
  proof (rule linorder_cases)
    assume "M < N"
    hence "D(M) < D(Suc M)" by (rule 1 [rule_format])
    also have "D(Suc M) = D(M)" by (rule 4 [rule_format], simp)
    finally show "M = N" by simp
  next
    assume "N < M"
    hence "D(N) < D(Suc N)" by (rule 3 [rule_format])
    also have "D(Suc N) = D(N)" by (rule 2 [rule_format], simp)
    finally show "M = N" by simp
  next
    assume "M = N" thus "M = N" .
  qed
qed

lemma partition_zero [simp]: "a = b ==> psize (%n. if n = 0 then a else b) = 0"
by (rule psize_unique, simp_all)

lemma partition_one [simp]: "a < b ==> psize (%n. if n = 0 then a else b) = 1"
by (rule psize_unique, simp_all)

lemma partition_single [simp]:
     "a \<le> b ==> partition(a,b)(%n. if n = 0 then a else b)"
by (auto simp add: partition_def order_le_less)

lemma partition_lhs: "partition(a,b) D ==> (D(0) = a)"
by (simp add: partition_def)

lemma partition:
       "(partition(a,b) D) =
        ((D 0 = a) &
         (\<forall>n < psize D. D n < D(Suc n)) &
         (\<forall>n \<ge> psize D. D n = b))"
apply (simp add: partition_def)
apply (rule iffI, clarify)
apply (subgoal_tac "psize D = N", simp)
apply (rule psize_unique, assumption, simp)
apply (simp, rule_tac x="psize D" in exI, simp)
done

lemma partition_rhs: "partition(a,b) D ==> (D(psize D) = b)"
by (simp add: partition)

lemma partition_rhs2: "[|partition(a,b) D; psize D \<le> n |] ==> (D n = b)"
by (simp add: partition)

lemma lemma_partition_lt_gen [rule_format]:
 "partition(a,b) D & m + Suc d \<le> n & n \<le> (psize D) --> D(m) < D(m + Suc d)"
apply (induct "d", auto simp add: partition)
apply (blast dest: Suc_le_lessD  intro: less_le_trans order_less_trans)
done

lemma less_eq_add_Suc: "m < n ==> \<exists>d. n = m + Suc d"
by (auto simp add: less_iff_Suc_add)

lemma partition_lt_gen:
     "[|partition(a,b) D; m < n; n \<le> (psize D)|] ==> D(m) < D(n)"
by (auto dest: less_eq_add_Suc intro: lemma_partition_lt_gen)

lemma partition_lt: "partition(a,b) D ==> n < (psize D) ==> D(0) < D(Suc n)"
apply (induct "n")
apply (auto simp add: partition)
done

lemma partition_le: "partition(a,b) D ==> a \<le> b"
apply (frule partition [THEN iffD1], safe)
apply (drule_tac x = "psize D" and P="%n. psize D \<le> n --> ?P n" in spec, safe)
apply (case_tac "psize D = 0")
apply (drule_tac [2] n = "psize D - Suc 0" in partition_lt, auto)
done

lemma partition_gt: "[|partition(a,b) D; n < (psize D)|] ==> D(n) < D(psize D)"
by (auto intro: partition_lt_gen)

lemma partition_eq: "partition(a,b) D ==> ((a = b) = (psize D = 0))"
apply (frule partition [THEN iffD1], safe)
apply (rotate_tac 2)
apply (drule_tac x = "psize D" in spec)
apply (rule ccontr)
apply (drule_tac n = "psize D - Suc 0" in partition_lt)
apply auto
done

lemma partition_lb: "partition(a,b) D ==> a \<le> D(r)"
apply (frule partition [THEN iffD1], safe)
apply (induct "r")
apply (cut_tac [2] y = "Suc r" and x = "psize D" in linorder_le_less_linear)
apply (auto intro: partition_le)
apply (drule_tac x = r in spec)
apply arith; 
done

lemma partition_lb_lt: "[| partition(a,b) D; psize D ~= 0 |] ==> a < D(Suc n)"
apply (rule_tac t = a in partition_lhs [THEN subst], assumption)
apply (cut_tac x = "Suc n" and y = "psize D" in linorder_le_less_linear)
apply (frule partition [THEN iffD1], safe)
 apply (blast intro: partition_lt less_le_trans)
apply (rotate_tac 3)
apply (drule_tac x = "Suc n" in spec)
apply (erule impE)
apply (erule less_imp_le)
apply (frule partition_rhs)
apply (drule partition_gt[of _ _ _ 0], arith)
apply (simp (no_asm_simp))
done

lemma partition_ub: "partition(a,b) D ==> D(r) \<le> b"
apply (frule partition [THEN iffD1])
apply (cut_tac x = "psize D" and y = r in linorder_le_less_linear, safe, blast)
apply (subgoal_tac "\<forall>x. D ((psize D) - x) \<le> b")
apply (rotate_tac 4)
apply (drule_tac x = "psize D - r" in spec)
apply (subgoal_tac "psize D - (psize D - r) = r")
apply simp
apply arith
apply safe
apply (induct_tac "x")
apply (simp (no_asm), blast)
apply (case_tac "psize D - Suc n = 0")
apply (erule_tac V = "\<forall>n. psize D \<le> n --> D n = b" in thin_rl)
apply (simp (no_asm_simp) add: partition_le)
apply (rule order_trans)
 prefer 2 apply assumption
apply (subgoal_tac "psize D - n = Suc (psize D - Suc n)")
 prefer 2 apply arith
apply (drule_tac x = "psize D - Suc n" in spec, simp) 
done

lemma partition_ub_lt: "[| partition(a,b) D; n < psize D |] ==> D(n) < b"
by (blast intro: partition_rhs [THEN subst] partition_gt)

lemma lemma_partition_append1:
     "[| partition (a, b) D1; partition (b, c) D2 |]
       ==> (\<forall>n < psize D1 + psize D2.
             (if n < psize D1 then D1 n else D2 (n - psize D1))
             < (if Suc n < psize D1 then D1 (Suc n)
                else D2 (Suc n - psize D1))) &
         (\<forall>n \<ge> psize D1 + psize D2.
             (if n < psize D1 then D1 n else D2 (n - psize D1)) =
             (if psize D1 + psize D2 < psize D1 then D1 (psize D1 + psize D2)
              else D2 (psize D1 + psize D2 - psize D1)))"
apply (auto intro: partition_lt_gen)
apply (subgoal_tac "psize D1 = Suc n")
apply (auto intro!: partition_lt_gen simp add: partition_lhs partition_ub_lt)
apply (auto intro!: partition_rhs2 simp add: partition_rhs
            split: nat_diff_split)
done

lemma lemma_psize1:
     "[| partition (a, b) D1; partition (b, c) D2; N < psize D1 |]
      ==> D1(N) < D2 (psize D2)"
apply (rule_tac y = "D1 (psize D1)" in order_less_le_trans)
apply (erule partition_gt)
apply (auto simp add: partition_rhs partition_le)
done

lemma lemma_partition_append2:
     "[| partition (a, b) D1; partition (b, c) D2 |]
      ==> psize (%n. if n < psize D1 then D1 n else D2 (n - psize D1)) =
          psize D1 + psize D2"
apply (rule psize_unique)
apply (erule (1) lemma_partition_append1 [THEN conjunct1])
apply (erule (1) lemma_partition_append1 [THEN conjunct2])
done

lemma tpart_eq_lhs_rhs: "[|psize D = 0; tpart(a,b) (D,p)|] ==> a = b"
by (auto simp add: tpart_def partition_eq)

lemma tpart_partition: "tpart(a,b) (D,p) ==> partition(a,b) D"
by (simp add: tpart_def)

lemma partition_append:
     "[| tpart(a,b) (D1,p1); fine(g) (D1,p1);
         tpart(b,c) (D2,p2); fine(g) (D2,p2) |]
       ==> \<exists>D p. tpart(a,c) (D,p) & fine(g) (D,p)"
apply (rule_tac x = "%n. if n < psize D1 then D1 n else D2 (n - psize D1)"
       in exI)
apply (rule_tac x = "%n. if n < psize D1 then p1 n else p2 (n - psize D1)"
       in exI)
apply (case_tac "psize D1 = 0")
apply (auto dest: tpart_eq_lhs_rhs)
 prefer 2
apply (simp add: fine_def
                 lemma_partition_append2 [OF tpart_partition tpart_partition])
  --{*But must not expand @{term fine} in other subgoals*}
apply auto
apply (subgoal_tac "psize D1 = Suc n")
 prefer 2 apply arith
apply (drule tpart_partition [THEN partition_rhs])
apply (drule tpart_partition [THEN partition_lhs])
apply (auto split: nat_diff_split)
apply (auto simp add: tpart_def)
defer 1
 apply (subgoal_tac "psize D1 = Suc n")
  prefer 2 apply arith
 apply (drule partition_rhs)
 apply (drule partition_lhs, auto)
apply (simp split: nat_diff_split)
apply (subst partition) 
apply (subst (1 2) lemma_partition_append2, assumption+)
apply (rule conjI) 
apply (simp add: partition_lhs)
apply (drule lemma_partition_append1)
apply assumption; 
apply (simp add: partition_rhs)
done


text{*We can always find a division that is fine wrt any gauge*}

lemma partition_exists:
     "[| a \<le> b; gauge {a..b} g |]
      ==> \<exists>D p. tpart(a,b) (D,p) & fine g (D,p)"
apply (cut_tac P = "%(u,v). a \<le> u & v \<le> b --> 
                   (\<exists>D p. tpart (u,v) (D,p) & fine (g) (D,p))" 
       in lemma_BOLZANO2)
apply safe
apply (blast intro: order_trans)+
apply (auto intro: partition_append)
apply (case_tac "a \<le> x & x \<le> b")
apply (rule_tac [2] x = 1 in exI, auto)
apply (rule_tac x = "g x" in exI)
apply (auto simp add: gauge_def)
apply (rule_tac x = "%n. if n = 0 then aa else ba" in exI)
apply (rule_tac x = "%n. if n = 0 then x else ba" in exI)
apply (auto simp add: tpart_def fine_def)
done

text{*Lemmas about combining gauges*}

lemma gauge_min:
     "[| gauge(E) g1; gauge(E) g2 |]
      ==> gauge(E) (%x. if g1(x) < g2(x) then g1(x) else g2(x))"
by (simp add: gauge_def)

lemma fine_min:
      "fine (%x. if g1(x) < g2(x) then g1(x) else g2(x)) (D,p)
       ==> fine(g1) (D,p) & fine(g2) (D,p)"
by (auto simp add: fine_def split: split_if_asm)


text{*The integral is unique if it exists*}

lemma Integral_unique:
    "[| a \<le> b; Integral(a,b) f k1; Integral(a,b) f k2 |] ==> k1 = k2"
apply (simp add: Integral_def)
apply (drule_tac x = "\<bar>k1 - k2\<bar> /2" in spec)+
apply auto
apply (drule gauge_min, assumption)
apply (drule_tac g = "%x. if g x < ga x then g x else ga x" 
       in partition_exists, assumption, auto)
apply (drule fine_min)
apply (drule spec)+
apply auto
apply (subgoal_tac "\<bar>(rsum (D,p) f - k2) - (rsum (D,p) f - k1)\<bar> < \<bar>k1 - k2\<bar>")
apply arith
apply (drule add_strict_mono, assumption)
apply (auto simp only: left_distrib [symmetric] mult_2_right [symmetric] 
                mult_less_cancel_right)
done

lemma Integral_zero [simp]: "Integral(a,a) f 0"
apply (auto simp add: Integral_def)
apply (rule_tac x = "%x. 1" in exI)
apply (auto dest: partition_eq simp add: gauge_def tpart_def rsum_def)
done

lemma sumr_partition_eq_diff_bounds [simp]:
     "(\<Sum>n=0..<m. D (Suc n) - D n::real) = D(m) - D 0"
by (induct "m", auto)

lemma Integral_eq_diff_bounds: "a \<le> b ==> Integral(a,b) (%x. 1) (b - a)"
apply (auto simp add: order_le_less rsum_def Integral_def)
apply (rule_tac x = "%x. b - a" in exI)
apply (auto simp add: gauge_def abs_less_iff tpart_def partition)
done

lemma Integral_mult_const: "a \<le> b ==> Integral(a,b) (%x. c)  (c*(b - a))"
apply (auto simp add: order_le_less rsum_def Integral_def)
apply (rule_tac x = "%x. b - a" in exI)
apply (auto simp add: setsum_right_distrib [symmetric] gauge_def abs_less_iff 
               right_diff_distrib [symmetric] partition tpart_def)
done

lemma Integral_mult:
     "[| a \<le> b; Integral(a,b) f k |] ==> Integral(a,b) (%x. c * f x) (c * k)"
apply (auto simp add: order_le_less 
            dest: Integral_unique [OF order_refl Integral_zero])
apply (auto simp add: Integral_def setsum_right_distrib[symmetric] mult_assoc)
apply (case_tac "c = 0", force)
apply (drule_tac x = "e/abs c" in spec)
apply (simp add: divide_pos_pos)
apply clarify
apply (rule_tac x="g" in exI, clarify)
apply (drule_tac x="D" in spec, drule_tac x="p" in spec)
apply (simp add: pos_less_divide_eq abs_mult [symmetric]
                 algebra_simps rsum_right_distrib)
done

text{*Fundamental theorem of calculus (Part I)*}

text{*"Straddle Lemma" : Swartz and Thompson: AMM 95(7) 1988 *}

lemma strad1:
       "\<lbrakk>\<forall>z::real. z \<noteq> x \<and> \<bar>z - x\<bar> < s \<longrightarrow>
             \<bar>(f z - f x) / (z - x) - f' x\<bar> < e/2;
        0 < s; 0 < e; a \<le> x; x \<le> b\<rbrakk>
       \<Longrightarrow> \<forall>z. \<bar>z - x\<bar> < s -->\<bar>f z - f x - f' x * (z - x)\<bar> \<le> e/2 * \<bar>z - x\<bar>"
apply clarify
apply (case_tac "z = x", simp)
apply (drule_tac x = z in spec)
apply (rule_tac z1 = "\<bar>inverse (z - x)\<bar>" 
       in real_mult_le_cancel_iff2 [THEN iffD1])
 apply simp
apply (simp del: abs_inverse abs_mult add: abs_mult [symmetric]
          mult_assoc [symmetric])
apply (subgoal_tac "inverse (z - x) * (f z - f x - f' x * (z - x)) 
                    = (f z - f x) / (z - x) - f' x")
 apply (simp add: abs_mult [symmetric] mult_ac diff_minus)
apply (subst mult_commute)
apply (simp add: left_distrib diff_minus)
apply (simp add: mult_assoc divide_inverse)
apply (simp add: left_distrib)
done

lemma lemma_straddle:
  assumes f': "\<forall>x. a \<le> x & x \<le> b --> DERIV f x :> f'(x)" and "0 < e"
  shows "\<exists>g. gauge {a..b} g &
                (\<forall>x u v. a \<le> u & u \<le> x & x \<le> v & v \<le> b & (v - u) < g(x)
                  --> \<bar>(f(v) - f(u)) - (f'(x) * (v - u))\<bar> \<le> e * (v - u))"
proof -
  have "\<forall>x\<in>{a..b}.
        (\<exists>d > 0. \<forall>u v. u \<le> x & x \<le> v & (v - u) < d --> 
                       \<bar>(f(v) - f(u)) - (f'(x) * (v - u))\<bar> \<le> e * (v - u))"
  proof (clarsimp)
    fix x :: real assume "a \<le> x" and "x \<le> b"
    with f' have "DERIV f x :> f'(x)" by simp
    then have "\<forall>r>0. \<exists>s>0. \<forall>z. z \<noteq> x \<and> \<bar>z - x\<bar> < s \<longrightarrow> \<bar>(f z - f x) / (z - x) - f' x\<bar> < r"
      by (simp add: DERIV_iff2 LIM_def)
    with `0 < e` obtain s
    where "\<forall>z. z \<noteq> x \<and> \<bar>z - x\<bar> < s \<longrightarrow> \<bar>(f z - f x) / (z - x) - f' x\<bar> < e/2" and "0 < s"
      by (drule_tac x="e/2" in spec, auto)
    then have strad [rule_format]:
        "\<forall>z. \<bar>z - x\<bar> < s --> \<bar>f z - f x - f' x * (z - x)\<bar> \<le> e/2 * \<bar>z - x\<bar>"
      using `0 < e` `a \<le> x` `x \<le> b` by (rule strad1)
    show "\<exists>d>0. \<forall>u v. u \<le> x \<and> x \<le> v \<and> v - u < d \<longrightarrow> \<bar>f v - f u - f' x * (v - u)\<bar> \<le> e * (v - u)"
    proof (safe intro!: exI)
      show "0 < s" by fact
    next
      fix u v :: real assume "u \<le> x" and "x \<le> v" and "v - u < s"
      have "\<bar>f v - f u - f' x * (v - u)\<bar> =
            \<bar>(f v - f x - f' x * (v - x)) + (f x - f u - f' x * (x - u))\<bar>"
        by (simp add: right_diff_distrib)
      also have "\<dots> \<le> \<bar>f v - f x - f' x * (v - x)\<bar> + \<bar>f x - f u - f' x * (x - u)\<bar>"
        by (rule abs_triangle_ineq)
      also have "\<dots> = \<bar>f v - f x - f' x * (v - x)\<bar> + \<bar>f u - f x - f' x * (u - x)\<bar>"
        by (simp add: right_diff_distrib)
      also have "\<dots> \<le> (e/2) * \<bar>v - x\<bar> + (e/2) * \<bar>u - x\<bar>"
        using `u \<le> x` `x \<le> v` `v - u < s` by (intro add_mono strad, simp_all)
      also have "\<dots> \<le> e * (v - u) / 2 + e * (v - u) / 2"
        using `u \<le> x` `x \<le> v` `0 < e` by (intro add_mono, simp_all)
      also have "\<dots> = e * (v - u)"
        by simp
      finally show "\<bar>f v - f u - f' x * (v - u)\<bar> \<le> e * (v - u)" .
    qed
  qed
  thus ?thesis
    by (simp add: gauge_def) (drule bchoice, auto)
qed

lemma FTC1: "[|a \<le> b; \<forall>x. a \<le> x & x \<le> b --> DERIV f x :> f'(x) |]
             ==> Integral(a,b) f' (f(b) - f(a))"
 apply (drule order_le_imp_less_or_eq, auto)
 apply (auto simp add: Integral_def2)
 apply (drule_tac e = "e / (b - a)" in lemma_straddle)
  apply (simp add: divide_pos_pos)
 apply clarify
 apply (rule_tac x="g" in exI, clarify)
 apply (clarsimp simp add: tpart_def rsum_def)
 apply (subgoal_tac "(\<Sum>n=0..<psize D. f(D(Suc n)) - f(D n)) = f b - f a")
  prefer 2
  apply (cut_tac D = "%n. f (D n)" and m = "psize D"
        in sumr_partition_eq_diff_bounds)
  apply (simp add: partition_lhs partition_rhs)
 apply (erule subst)
 apply (subst setsum_subtractf [symmetric])
 apply (rule setsum_abs [THEN order_trans])
 apply (subgoal_tac "e = (\<Sum>n=0..<psize D. (e / (b - a)) * (D (Suc n) - (D n)))")
  apply (erule ssubst)
  apply (simp add: abs_minus_commute)
  apply (rule setsum_mono)
  apply (simp add: partition_lb partition_ub fine_def)
 apply (subst setsum_right_distrib [symmetric])
 apply (subst sumr_partition_eq_diff_bounds)
 apply (simp add: partition_lhs partition_rhs)
done


lemma Integral_subst: "[| Integral(a,b) f k1; k2=k1 |] ==> Integral(a,b) f k2"
by simp

lemma Integral_add:
     "[| a \<le> b; b \<le> c; Integral(a,b) f' k1; Integral(b,c) f' k2;
         \<forall>x. a \<le> x & x \<le> c --> DERIV f x :> f' x |]
     ==> Integral(a,c) f' (k1 + k2)"
apply (rule FTC1 [THEN Integral_subst], auto)
apply (frule FTC1, auto)
apply (frule_tac a = b in FTC1, auto)
apply (drule_tac x = x in spec, auto)
apply (drule_tac ?k2.0 = "f b - f a" in Integral_unique)
apply (drule_tac [3] ?k2.0 = "f c - f b" in Integral_unique, auto)
done

lemma partition_psize_Least:
     "partition(a,b) D ==> psize D = (LEAST n. D(n) = b)"
apply (auto intro!: Least_equality [symmetric] partition_rhs)
apply (auto dest: partition_ub_lt simp add: linorder_not_less [symmetric])
done

lemma lemma_partition_bounded: "partition (a, c) D ==> ~ (\<exists>n. c < D(n))"
apply safe
apply (drule_tac r = n in partition_ub, auto)
done

lemma lemma_partition_eq:
     "partition (a, c) D ==> D = (%n. if D n < c then D n else c)"
apply (rule ext, auto)
apply (auto dest!: lemma_partition_bounded)
apply (drule_tac x = n in spec, auto)
done

lemma lemma_partition_eq2:
     "partition (a, c) D ==> D = (%n. if D n \<le> c then D n else c)"
apply (rule ext, auto)
apply (auto dest!: lemma_partition_bounded)
apply (drule_tac x = n in spec, auto)
done

lemma partition_lt_Suc:
     "[| partition(a,b) D; n < psize D |] ==> D n < D (Suc n)"
by (auto simp add: partition)

lemma tpart_tag_eq: "tpart(a,c) (D,p) ==> p = (%n. if D n < c then p n else c)"
apply (rule ext)
apply (auto simp add: tpart_def)
apply (drule linorder_not_less [THEN iffD1])
apply (drule_tac r = "Suc n" in partition_ub)
apply (drule_tac x = n in spec, auto)
done

subsection{*Lemmas for Additivity Theorem of Gauge Integral*}

lemma lemma_additivity1:
     "[| a \<le> D n; D n < b; partition(a,b) D |] ==> n < psize D"
by (auto simp add: partition linorder_not_less [symmetric])

lemma lemma_additivity2: "[| a \<le> D n; partition(a,D n) D |] ==> psize D \<le> n"
apply (rule ccontr, drule not_leE)
apply (frule partition [THEN iffD1], safe)
apply (frule_tac r = "Suc n" in partition_ub)
apply (auto dest!: spec)
done

lemma partition_eq_bound:
     "[| partition(a,b) D; psize D < m |] ==> D(m) = D(psize D)"
by (auto simp add: partition)

lemma partition_ub2: "[| partition(a,b) D; psize D < m |] ==> D(r) \<le> D(m)"
by (simp add: partition partition_ub)

lemma tag_point_eq_partition_point:
    "[| tpart(a,b) (D,p); psize D \<le> m |] ==> p(m) = D(m)"
apply (simp add: tpart_def, auto)
apply (drule_tac x = m in spec)
apply (auto simp add: partition_rhs2)
done

lemma partition_lt_cancel: "[| partition(a,b) D; D m < D n |] ==> m < n"
apply (cut_tac less_linear [of n "psize D"], auto)
apply (cut_tac less_linear [of m n])
apply (cut_tac less_linear [of m "psize D"])
apply (auto dest: partition_gt)
apply (drule_tac n = m in partition_lt_gen, auto)
apply (frule partition_eq_bound)
apply (drule_tac [2] partition_gt, auto)
apply (metis linear not_less partition_rhs partition_rhs2)
apply (metis lemma_additivity1 order_less_trans partition_eq_bound partition_lb partition_rhs)
done

lemma lemma_additivity4_psize_eq:
     "[| a \<le> D n; D n < b; partition (a, b) D |]
      ==> psize (%x. if D x < D n then D(x) else D n) = n"
apply (frule (2) lemma_additivity1)
apply (rule psize_unique, auto)
apply (erule partition_lt_Suc, erule (1) less_trans)
apply (erule notE)
apply (erule (1) partition_lt_gen, erule less_imp_le)
apply (drule (1) partition_lt_cancel, simp)
done

lemma lemma_psize_left_less_psize:
     "partition (a, b) D
      ==> psize (%x. if D x < D n then D(x) else D n) \<le> psize D"
apply (frule_tac r = n in partition_ub)
apply (drule_tac x = "D n" in order_le_imp_less_or_eq)
apply (auto simp add: lemma_partition_eq [symmetric])
apply (frule_tac r = n in partition_lb)
apply (drule (2) lemma_additivity4_psize_eq)  
apply (rule ccontr, auto)
apply (frule_tac not_leE [THEN [2] partition_eq_bound])
apply (auto simp add: partition_rhs)
done

lemma lemma_psize_left_less_psize2:
     "[| partition(a,b) D; na < psize (%x. if D x < D n then D(x) else D n) |]
      ==> na < psize D"
by (erule lemma_psize_left_less_psize [THEN [2] less_le_trans])


lemma lemma_additivity3:
     "[| partition(a,b) D; D na < D n; D n < D (Suc na);
         n < psize D |]
      ==> False"
by (metis not_less_eq partition_lt_cancel real_of_nat_less_iff)


lemma psize_const [simp]: "psize (%x. k) = 0"
by (auto simp add: psize_def)

lemma lemma_additivity3a:
     "[| partition(a,b) D; D na < D n; D n < D (Suc na);
         na < psize D |]
      ==> False"
apply (frule_tac m = n in partition_lt_cancel)
apply (auto intro: lemma_additivity3)
done

lemma better_lemma_psize_right_eq1:
     "[| partition(a,b) D; D n < b |] ==> psize (%x. D (x + n)) \<le> psize D - n"
apply (simp add: psize_def [of "(%x. D (x + n))"]);
apply (rule_tac a = "psize D - n" in someI2, auto)
  apply (simp add: partition less_diff_conv)
 apply (simp add: le_diff_conv partition_rhs2 split: nat_diff_split)
apply (drule_tac x = "psize D - n" in spec, auto)
apply (frule partition_rhs, safe)
apply (frule partition_lt_cancel, assumption)
apply (drule partition [THEN iffD1], safe)
apply (subgoal_tac "~ D (psize D - n + n) < D (Suc (psize D - n + n))")
 apply blast
apply (drule_tac x = "Suc (psize D)" and P="%n. ?P n \<longrightarrow> D n = D (psize D)"
       in spec)
apply simp
done

lemma psize_le_n: "partition (a, D n) D ==> psize D \<le> n" 
apply (rule ccontr, drule not_leE)
apply (frule partition_lt_Suc, assumption)
apply (frule_tac r = "Suc n" in partition_ub, auto)
done

lemma better_lemma_psize_right_eq1a:
     "partition(a,D n) D ==> psize (%x. D (x + n)) \<le> psize D - n"
apply (simp add: psize_def [of "(%x. D (x + n))"]);
apply (rule_tac a = "psize D - n" in someI2, auto)
  apply (simp add: partition less_diff_conv)
 apply (simp add: le_diff_conv)
apply (case_tac "psize D \<le> n")
  apply (force intro: partition_rhs2)
 apply (simp add: partition linorder_not_le)
apply (rule ccontr, drule not_leE)
apply (frule psize_le_n)
apply (drule_tac x = "psize D - n" in spec, simp)
apply (drule partition [THEN iffD1], safe)
apply (drule_tac x = "Suc n" and P="%na. ?s \<le> na \<longrightarrow> D na = D n" in spec, auto)
done

lemma better_lemma_psize_right_eq:
     "partition(a,b) D ==> psize (%x. D (x + n)) \<le> psize D - n"
apply (frule_tac r1 = n in partition_ub [THEN order_le_imp_less_or_eq])
apply (blast intro: better_lemma_psize_right_eq1a better_lemma_psize_right_eq1)
done

lemma lemma_psize_right_eq1:
     "[| partition(a,b) D; D n < b |] ==> psize (%x. D (x + n)) \<le> psize D"
apply (simp add: psize_def [of "(%x. D (x + n))"])
apply (rule_tac a = "psize D - n" in someI2, auto)
  apply (simp add: partition less_diff_conv)
 apply (subgoal_tac "n \<le> psize D")
  apply (simp add: partition le_diff_conv)
 apply (rule ccontr, drule not_leE)
 apply (drule_tac less_imp_le [THEN [2] partition_rhs2], assumption, simp)
apply (drule_tac x = "psize D" in spec)
apply (simp add: partition)
done

(* should be combined with previous theorem; also proof has redundancy *)
lemma lemma_psize_right_eq1a:
     "partition(a,D n) D ==> psize (%x. D (x + n)) \<le> psize D"
apply (simp add: psize_def [of "(%x. D (x + n))"]);
apply (rule_tac a = "psize D - n" in someI2, auto)
  apply (simp add: partition less_diff_conv)
 apply (case_tac "psize D \<le> n")
  apply (force intro: partition_rhs2 simp add: le_diff_conv)
 apply (simp add: partition le_diff_conv)
apply (rule ccontr, drule not_leE)
apply (drule_tac x = "psize D" in spec)
apply (simp add: partition)
done

lemma lemma_psize_right_eq:
     "[| partition(a,b) D |] ==> psize (%x. D (x + n)) \<le> psize D"
apply (frule_tac r1 = n in partition_ub [THEN order_le_imp_less_or_eq])
apply (blast intro: lemma_psize_right_eq1a lemma_psize_right_eq1)
done

lemma tpart_left1:
     "[| a \<le> D n; tpart (a, b) (D, p) |]
      ==> tpart(a, D n) (%x. if D x < D n then D(x) else D n,
          %x. if D x < D n then p(x) else D n)"
apply (frule_tac r = n in tpart_partition [THEN partition_ub])
apply (drule_tac x = "D n" in order_le_imp_less_or_eq)
apply (auto simp add: tpart_partition [THEN lemma_partition_eq, symmetric] tpart_tag_eq [symmetric])
apply (frule_tac tpart_partition [THEN [3] lemma_additivity1])
apply (auto simp add: tpart_def)
apply (drule_tac [2] linorder_not_less [THEN iffD1, THEN order_le_imp_less_or_eq], auto)
  prefer 3 apply (drule_tac x=na in spec, arith)
 prefer 2 apply (blast dest: lemma_additivity3)
apply (frule (2) lemma_additivity4_psize_eq)
apply (rule partition [THEN iffD2])
apply (frule partition [THEN iffD1])
apply safe 
apply (auto simp add: partition_lt_gen)  
apply (drule (1) partition_lt_cancel, arith)
done

lemma fine_left1:
     "[| a \<le> D n; tpart (a, b) (D, p); gauge {a..D n} g;
         fine (%x. if x < D n then min (g x) ((D n - x)/ 2)
                 else if x = D n then min (g (D n)) (ga (D n))
                      else min (ga x) ((x - D n)/ 2)) (D, p) |]
      ==> fine g
           (%x. if D x < D n then D(x) else D n,
            %x. if D x < D n then p(x) else D n)"
apply (auto simp add: fine_def tpart_def gauge_def)
apply (frule_tac [!] na=na in lemma_psize_left_less_psize2)
apply (drule_tac [!] x = na in spec, auto)
apply (drule_tac [!] x = na in spec, auto)
apply (auto dest: lemma_additivity3a simp add: split_if_asm)
done

lemma tpart_right1:
     "[| a \<le> D n; tpart (a, b) (D, p) |]
      ==> tpart(D n, b) (%x. D(x + n),%x. p(x + n))"
apply (simp add: tpart_def partition_def, safe)
apply (rule_tac x = "N - n" in exI, auto)
done

lemma fine_right1:
     "[| a \<le> D n; tpart (a, b) (D, p); gauge {D n..b} ga;
         fine (%x. if x < D n then min (g x) ((D n - x)/ 2)
                 else if x = D n then min (g (D n)) (ga (D n))
                      else min (ga x) ((x - D n)/ 2)) (D, p) |]
      ==> fine ga (%x. D(x + n),%x. p(x + n))"
apply (auto simp add: fine_def gauge_def)
apply (drule_tac x = "na + n" in spec)
apply (frule_tac n = n in tpart_partition [THEN better_lemma_psize_right_eq], auto)
apply (simp add: tpart_def, safe)
apply (subgoal_tac "D n \<le> p (na + n)")
apply (drule_tac y = "p (na + n)" in order_le_imp_less_or_eq)
apply safe
apply (simp split: split_if_asm, simp)
apply (drule less_le_trans, assumption)
apply (rotate_tac 5)
apply (drule_tac x = "na + n" in spec, safe)
apply (rule_tac y="D (na + n)" in order_trans)
apply (case_tac "na = 0", auto)
apply (erule partition_lt_gen [THEN order_less_imp_le])
apply arith
apply arith
done

text{* Bartle/Sherbert: Theorem 10.1.5 p. 278 *}
lemma Integral_add_fun:
    "[| a \<le> b; Integral(a,b) f k1; Integral(a,b) g k2 |]
     ==> Integral(a,b) (%x. f x + g x) (k1 + k2)"
apply (simp add: Integral_def, auto)
apply ((drule_tac x = "e/2" in spec)+)
apply auto
apply (drule gauge_min, assumption)
apply (rule_tac x = " (%x. if ga x < gaa x then ga x else gaa x)" in exI)
apply auto
apply (drule fine_min)
apply ((drule spec)+, auto)
apply (drule_tac a = "\<bar>rsum (D, p) f - k1\<bar> * 2" and c = "\<bar>rsum (D, p) g - k2\<bar> * 2" in add_strict_mono, assumption)
apply (auto simp only: rsum_add left_distrib [symmetric]
                mult_2_right [symmetric] real_mult_less_iff1)
done

lemma partition_lt_gen2:
     "[| partition(a,b) D; r < psize D |] ==> 0 < D (Suc r) - D r"
by (auto simp add: partition)

lemma lemma_Integral_le:
     "[| \<forall>x. a \<le> x & x \<le> b --> f x \<le> g x;
         tpart(a,b) (D,p)
      |] ==> \<forall>n \<le> psize D. f (p n) \<le> g (p n)"
apply (simp add: tpart_def)
apply (auto, frule partition [THEN iffD1], auto)
apply (drule_tac x = "p n" in spec, auto)
apply (case_tac "n = 0", simp)
apply (rule partition_lt_gen [THEN order_less_le_trans, THEN order_less_imp_le], auto)
apply (drule le_imp_less_or_eq, auto)
apply (drule_tac [2] x = "psize D" in spec, auto)
apply (drule_tac r = "Suc n" in partition_ub)
apply (drule_tac x = n in spec, auto)
done

lemma lemma_Integral_rsum_le:
     "[| \<forall>x. a \<le> x & x \<le> b --> f x \<le> g x;
         tpart(a,b) (D,p)
      |] ==> rsum(D,p) f \<le> rsum(D,p) g"
apply (simp add: rsum_def)
apply (auto intro!: setsum_mono dest: tpart_partition [THEN partition_lt_gen2]
               dest!: lemma_Integral_le)
done

lemma Integral_le:
    "[| a \<le> b;
        \<forall>x. a \<le> x & x \<le> b --> f(x) \<le> g(x);
        Integral(a,b) f k1; Integral(a,b) g k2
     |] ==> k1 \<le> k2"
apply (simp add: Integral_def)
apply (rotate_tac 2)
apply (drule_tac x = "\<bar>k1 - k2\<bar> /2" in spec)
apply (drule_tac x = "\<bar>k1 - k2\<bar> /2" in spec, auto)
apply (drule gauge_min, assumption)
apply (drule_tac g = "%x. if ga x < gaa x then ga x else gaa x" 
       in partition_exists, assumption, auto)
apply (drule fine_min)
apply (drule_tac x = D in spec, drule_tac x = D in spec)
apply (drule_tac x = p in spec, drule_tac x = p in spec, auto)
apply (frule lemma_Integral_rsum_le, assumption)
apply (subgoal_tac "\<bar>(rsum (D,p) f - k1) - (rsum (D,p) g - k2)\<bar> < \<bar>k1 - k2\<bar>")
apply arith
apply (drule add_strict_mono, assumption)
apply (auto simp only: left_distrib [symmetric] mult_2_right [symmetric]
                       real_mult_less_iff1)
done

lemma Integral_imp_Cauchy:
     "(\<exists>k. Integral(a,b) f k) ==>
      (\<forall>e > 0. \<exists>g. gauge {a..b} g &
                       (\<forall>D1 D2 p1 p2.
                            tpart(a,b) (D1, p1) & fine g (D1,p1) &
                            tpart(a,b) (D2, p2) & fine g (D2,p2) -->
                            \<bar>rsum(D1,p1) f - rsum(D2,p2) f\<bar> < e))"
apply (simp add: Integral_def, auto)
apply (drule_tac x = "e/2" in spec, auto)
apply (rule exI, auto)
apply (frule_tac x = D1 in spec)
apply (frule_tac x = D2 in spec)
apply ((drule spec)+, auto)
apply (erule_tac V = "0 < e" in thin_rl)
apply (drule add_strict_mono, assumption)
apply (auto simp only: left_distrib [symmetric] mult_2_right [symmetric]
                       real_mult_less_iff1)
done

lemma Cauchy_iff2:
     "Cauchy X =
      (\<forall>j. (\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. \<bar>X m - X n\<bar> < inverse(real (Suc j))))"
apply (simp add: Cauchy_def, auto)
apply (drule reals_Archimedean, safe)
apply (drule_tac x = n in spec, auto)
apply (rule_tac x = M in exI, auto)
apply (drule_tac x = m in spec, simp)
apply (drule_tac x = na in spec, auto)
done

lemma partition_exists2:
     "[| a \<le> b; \<forall>n. gauge {a..b} (fa n) |]
      ==> \<forall>n. \<exists>D p. tpart (a, b) (D, p) & fine (fa n) (D, p)"
by (blast dest: partition_exists) 

lemma monotonic_anti_derivative:
  fixes f g :: "real => real" shows
     "[| a \<le> b; \<forall>c. a \<le> c & c \<le> b --> f' c \<le> g' c;
         \<forall>x. DERIV f x :> f' x; \<forall>x. DERIV g x :> g' x |]
      ==> f b - f a \<le> g b - g a"
apply (rule Integral_le, assumption)
apply (auto intro: FTC1) 
done

end
