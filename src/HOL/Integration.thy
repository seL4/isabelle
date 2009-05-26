(*  Author      : Jacques D. Fleuriot
    Copyright   : 2000  University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{*Theory of Integration*}

theory Integration
imports Deriv ATP_Linkup
begin

text{*We follow John Harrison in formalizing the Gauge integral.*}

subsection {* Gauges *}

definition
  gauge :: "[real set, real => real] => bool" where
  [code del]:"gauge E g = (\<forall>x\<in>E. 0 < g(x))"


subsection {* Gauge-fine divisions *}

inductive
  fine :: "[real \<Rightarrow> real, real \<times> real, (real \<times> real \<times> real) list] \<Rightarrow> bool"
for
  \<delta> :: "real \<Rightarrow> real"
where
  fine_Nil:
    "fine \<delta> (a, a) []"
| fine_Cons:
    "\<lbrakk>fine \<delta> (b, c) D; a < b; a \<le> x; x \<le> b; b - a < \<delta> x\<rbrakk>
      \<Longrightarrow> fine \<delta> (a, c) ((a, x, b) # D)"

lemmas fine_induct [induct set: fine] =
  fine.induct [of "\<delta>" "(a,b)" "D" "split P", unfolded split_conv, standard]

lemma fine_single:
  "\<lbrakk>a < b; a \<le> x; x \<le> b; b - a < \<delta> x\<rbrakk> \<Longrightarrow> fine \<delta> (a, b) [(a, x, b)]"
by (rule fine_Cons [OF fine_Nil])

lemma fine_append:
  "\<lbrakk>fine \<delta> (a, b) D; fine \<delta> (b, c) D'\<rbrakk> \<Longrightarrow> fine \<delta> (a, c) (D @ D')"
by (induct set: fine, simp, simp add: fine_Cons)

lemma fine_imp_le: "fine \<delta> (a, b) D \<Longrightarrow> a \<le> b"
by (induct set: fine, simp_all)

lemma nonempty_fine_imp_less: "\<lbrakk>fine \<delta> (a, b) D; D \<noteq> []\<rbrakk> \<Longrightarrow> a < b"
apply (induct set: fine, simp)
apply (drule fine_imp_le, simp)
done

lemma empty_fine_imp_eq: "\<lbrakk>fine \<delta> (a, b) D; D = []\<rbrakk> \<Longrightarrow> a = b"
by (induct set: fine, simp_all)

lemma fine_eq: "fine \<delta> (a, b) D \<Longrightarrow> a = b \<longleftrightarrow> D = []"
apply (cases "D = []")
apply (drule (1) empty_fine_imp_eq, simp)
apply (drule (1) nonempty_fine_imp_less, simp)
done

lemma mem_fine:
  "\<lbrakk>fine \<delta> (a, b) D; (u, x, v) \<in> set D\<rbrakk> \<Longrightarrow> u < v \<and> u \<le> x \<and> x \<le> v"
by (induct set: fine, simp, force)

lemma mem_fine2: "\<lbrakk>fine \<delta> (a, b) D; (u, z, v) \<in> set D\<rbrakk> \<Longrightarrow> a \<le> u \<and> v \<le> b"
apply (induct arbitrary: z u v set: fine, auto)
apply (simp add: fine_imp_le)
apply (erule order_trans [OF less_imp_le], simp)
done

lemma mem_fine3: "\<lbrakk>fine \<delta> (a, b) D; (u, z, v) \<in> set D\<rbrakk> \<Longrightarrow> v - u < \<delta> z"
by (induct arbitrary: z u v set: fine) auto

lemma BOLZANO:
  fixes P :: "real \<Rightarrow> real \<Rightarrow> bool"
  assumes 1: "a \<le> b"
  assumes 2: "\<And>a b c. \<lbrakk>P a b; P b c; a \<le> b; b \<le> c\<rbrakk> \<Longrightarrow> P a c"
  assumes 3: "\<And>x. \<exists>d>0. \<forall>a b. a \<le> x & x \<le> b & (b-a) < d \<longrightarrow> P a b"
  shows "P a b"
apply (subgoal_tac "split P (a,b)", simp)
apply (rule lemma_BOLZANO [OF _ _ 1])
apply (clarify, erule (3) 2)
apply (clarify, rule 3)
done

text{*We can always find a division that is fine wrt any gauge*}

lemma fine_exists:
  assumes "a \<le> b" and "gauge {a..b} \<delta>" shows "\<exists>D. fine \<delta> (a, b) D"
proof -
  {
    fix u v :: real assume "u \<le> v"
    have "a \<le> u \<Longrightarrow> v \<le> b \<Longrightarrow> \<exists>D. fine \<delta> (u, v) D"
      apply (induct u v rule: BOLZANO, rule `u \<le> v`)
       apply (simp, fast intro: fine_append)
      apply (case_tac "a \<le> x \<and> x \<le> b")
       apply (rule_tac x="\<delta> x" in exI)
       apply (rule conjI)
        apply (simp add: `gauge {a..b} \<delta>` [unfolded gauge_def])
       apply (clarify, rename_tac u v)
       apply (case_tac "u = v")
        apply (fast intro: fine_Nil)
       apply (subgoal_tac "u < v", fast intro: fine_single, simp)
      apply (rule_tac x="1" in exI, clarsimp)
      done
  }
  with `a \<le> b` show ?thesis by auto
qed


subsection {* Riemann sum *}

definition
  rsum :: "[(real \<times> real \<times> real) list, real \<Rightarrow> real] \<Rightarrow> real" where
  "rsum D f = (\<Sum>(u, x, v)\<leftarrow>D. f x * (v - u))"

lemma rsum_Nil [simp]: "rsum [] f = 0"
unfolding rsum_def by simp

lemma rsum_Cons [simp]: "rsum ((u, x, v) # D) f = f x * (v - u) + rsum D f"
unfolding rsum_def by simp

lemma rsum_zero [simp]: "rsum D (\<lambda>x. 0) = 0"
by (induct D, auto)

lemma rsum_left_distrib: "rsum D f * c = rsum D (\<lambda>x. f x * c)"
by (induct D, auto simp add: algebra_simps)

lemma rsum_right_distrib: "c * rsum D f = rsum D (\<lambda>x. c * f x)"
by (induct D, auto simp add: algebra_simps)

lemma rsum_add: "rsum D (\<lambda>x. f x + g x) =  rsum D f + rsum D g"
by (induct D, auto simp add: algebra_simps)


subsection {* Gauge integrability (definite) *}

definition
  Integral :: "[(real*real),real=>real,real] => bool" where
  [code del]: "Integral = (%(a,b) f k. \<forall>e > 0.
                               (\<exists>\<delta>. gauge {a .. b} \<delta> &
                               (\<forall>D. fine \<delta> (a,b) D -->
                                         \<bar>rsum D f - k\<bar> < e)))"

lemma Integral_def2:
  "Integral = (%(a,b) f k. \<forall>e>0. (\<exists>\<delta>. gauge {a..b} \<delta> &
                               (\<forall>D. fine \<delta> (a,b) D -->
                                         \<bar>rsum D f - k\<bar> \<le> e)))"
unfolding Integral_def
apply (safe intro!: ext)
apply (fast intro: less_imp_le)
apply (drule_tac x="e/2" in spec)
apply force
done

text{*Lemmas about combining gauges*}

lemma gauge_min:
     "[| gauge(E) g1; gauge(E) g2 |]
      ==> gauge(E) (%x. min (g1(x)) (g2(x)))"
by (simp add: gauge_def)

lemma fine_min:
      "fine (%x. min (g1(x)) (g2(x))) (a,b) D
       ==> fine(g1) (a,b) D & fine(g2) (a,b) D"
apply (erule fine.induct)
apply (simp add: fine_Nil)
apply (simp add: fine_Cons)
done

text{*The integral is unique if it exists*}

lemma Integral_unique:
    "[| a \<le> b; Integral(a,b) f k1; Integral(a,b) f k2 |] ==> k1 = k2"
apply (simp add: Integral_def)
apply (drule_tac x = "\<bar>k1 - k2\<bar> /2" in spec)+
apply auto
apply (drule gauge_min, assumption)
apply (drule_tac \<delta> = "%x. min (\<delta> x) (\<delta>' x)"
       in fine_exists, assumption, auto)
apply (drule fine_min)
apply (drule spec)+
apply auto
apply (subgoal_tac "\<bar>(rsum D f - k2) - (rsum D f - k1)\<bar> < \<bar>k1 - k2\<bar>")
apply arith
apply (drule add_strict_mono, assumption)
apply (auto simp only: left_distrib [symmetric] mult_2_right [symmetric] 
                mult_less_cancel_right)
done

lemma Integral_zero [simp]: "Integral(a,a) f 0"
apply (auto simp add: Integral_def)
apply (rule_tac x = "%x. 1" in exI)
apply (auto dest: fine_eq simp add: gauge_def rsum_def)
done

lemma fine_rsum_const: "fine \<delta> (a,b) D \<Longrightarrow> rsum D (\<lambda>x. c) = (c * (b - a))"
unfolding rsum_def
by (induct set: fine, auto simp add: algebra_simps)

lemma Integral_eq_diff_bounds: "a \<le> b ==> Integral(a,b) (%x. 1) (b - a)"
apply (cases "a = b", simp)
apply (simp add: Integral_def, clarify)
apply (rule_tac x = "%x. b - a" in exI)
apply (rule conjI, simp add: gauge_def)
apply (clarify)
apply (subst fine_rsum_const, assumption, simp)
done

lemma Integral_mult_const: "a \<le> b ==> Integral(a,b) (%x. c)  (c*(b - a))"
apply (cases "a = b", simp)
apply (simp add: Integral_def, clarify)
apply (rule_tac x = "%x. b - a" in exI)
apply (rule conjI, simp add: gauge_def)
apply (clarify)
apply (subst fine_rsum_const, assumption, simp)
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
apply (rule_tac x="\<delta>" in exI, clarify)
apply (drule_tac x="D" in spec, clarify)
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

lemma fine_listsum_eq_diff:
  fixes f :: "real \<Rightarrow> real"
  shows "fine \<delta> (a, b) D \<Longrightarrow> (\<Sum>(u, x, v)\<leftarrow>D. f v - f u) = f b - f a"
by (induct set: fine) simp_all

lemma FTC1: "[|a \<le> b; \<forall>x. a \<le> x & x \<le> b --> DERIV f x :> f'(x) |]
             ==> Integral(a,b) f' (f(b) - f(a))"
 apply (drule order_le_imp_less_or_eq, auto)
 apply (auto simp add: Integral_def2)
 apply (drule_tac e = "e / (b - a)" in lemma_straddle)
  apply (simp add: divide_pos_pos)
 apply clarify
 apply (rule_tac x="g" in exI, clarify)
 apply (clarsimp simp add: rsum_def)
 apply (frule fine_listsum_eq_diff [where f=f])
 apply (erule subst)
 apply (subst listsum_subtractf [symmetric])
 apply (rule listsum_abs [THEN order_trans])
 apply (subst map_compose [symmetric, unfolded o_def])
 apply (subgoal_tac "e = (\<Sum>(u, x, v)\<leftarrow>D. (e / (b - a)) * (v - u))")
  apply (erule ssubst)
  apply (simp add: abs_minus_commute)
  apply (rule listsum_mono)
  apply (clarify, rename_tac u x v)
  apply ((drule spec)+, erule mp)
  apply (simp add: mem_fine mem_fine2 mem_fine3)
 apply (frule fine_listsum_eq_diff [where f="\<lambda>x. x"])
 apply (simp only: split_def)
 apply (subst listsum_const_mult)
 apply simp
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

subsection {* Additivity Theorem of Gauge Integral *}

text{* Bartle/Sherbert: Theorem 10.1.5 p. 278 *}
lemma Integral_add_fun:
    "[| a \<le> b; Integral(a,b) f k1; Integral(a,b) g k2 |]
     ==> Integral(a,b) (%x. f x + g x) (k1 + k2)"
unfolding Integral_def
apply clarify
apply (drule_tac x = "e/2" in spec)+
apply clarsimp
apply (rule_tac x = "\<lambda>x. min (\<delta> x) (\<delta>' x)" in exI)
apply (rule conjI, erule (1) gauge_min)
apply clarify
apply (drule fine_min)
apply (drule_tac x=D in spec, simp)+
apply (drule_tac a = "\<bar>rsum D f - k1\<bar> * 2" and c = "\<bar>rsum D g - k2\<bar> * 2" in add_strict_mono, assumption)
apply (auto simp only: rsum_add left_distrib [symmetric]
                mult_2_right [symmetric] real_mult_less_iff1)
done

lemma lemma_Integral_rsum_le:
     "[| \<forall>x. a \<le> x & x \<le> b --> f x \<le> g x;
         fine \<delta> (a,b) D
      |] ==> rsum D f \<le> rsum D g"
unfolding rsum_def
apply (rule listsum_mono)
apply clarify
apply (rule mult_right_mono)
apply (drule spec, erule mp)
apply (frule (1) mem_fine)
apply (frule (1) mem_fine2)
apply simp
apply (frule (1) mem_fine)
apply simp
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
apply (drule_tac \<delta> = "\<lambda>x. min (\<delta> x) (\<delta>' x)" in fine_exists, assumption, clarify)
apply (drule fine_min)
apply (drule_tac x = D in spec, drule_tac x = D in spec, clarsimp)
apply (frule lemma_Integral_rsum_le, assumption)
apply (subgoal_tac "\<bar>(rsum D f - k1) - (rsum D g - k2)\<bar> < \<bar>k1 - k2\<bar>")
apply arith
apply (drule add_strict_mono, assumption)
apply (auto simp only: left_distrib [symmetric] mult_2_right [symmetric]
                       real_mult_less_iff1)
done

lemma Integral_imp_Cauchy:
     "(\<exists>k. Integral(a,b) f k) ==>
      (\<forall>e > 0. \<exists>\<delta>. gauge {a..b} \<delta> &
                       (\<forall>D1 D2.
                            fine \<delta> (a,b) D1 &
                            fine \<delta> (a,b) D2 -->
                            \<bar>rsum D1 f - rsum D2 f\<bar> < e))"
apply (simp add: Integral_def, auto)
apply (drule_tac x = "e/2" in spec, auto)
apply (rule exI, auto)
apply (frule_tac x = D1 in spec)
apply (drule_tac x = D2 in spec)
apply simp
apply (thin_tac "0 < e")
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

lemma monotonic_anti_derivative:
  fixes f g :: "real => real" shows
     "[| a \<le> b; \<forall>c. a \<le> c & c \<le> b --> f' c \<le> g' c;
         \<forall>x. DERIV f x :> f' x; \<forall>x. DERIV g x :> g' x |]
      ==> f b - f a \<le> g b - g a"
apply (rule Integral_le, assumption)
apply (auto intro: FTC1) 
done

end
