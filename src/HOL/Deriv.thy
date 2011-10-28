(*  Title       : Deriv.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
    GMVT by Benjamin Porter, 2005
*)

header{* Differentiation *}

theory Deriv
imports Lim
begin

text{*Standard Definitions*}

definition
  deriv :: "['a::real_normed_field \<Rightarrow> 'a, 'a, 'a] \<Rightarrow> bool"
    --{*Differentiation: D is derivative of function f at x*}
          ("(DERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60) where
  "DERIV f x :> D = ((%h. (f(x + h) - f x) / h) -- 0 --> D)"

primrec
  Bolzano_bisect :: "(real \<times> real \<Rightarrow> bool) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<times> real" where
  "Bolzano_bisect P a b 0 = (a, b)"
  | "Bolzano_bisect P a b (Suc n) =
      (let (x, y) = Bolzano_bisect P a b n
       in if P (x, (x+y) / 2) then ((x+y)/2, y)
                              else (x, (x+y)/2))"


subsection {* Derivatives *}

lemma DERIV_iff: "(DERIV f x :> D) = ((%h. (f(x + h) - f(x))/h) -- 0 --> D)"
by (simp add: deriv_def)

lemma DERIV_D: "DERIV f x :> D ==> (%h. (f(x + h) - f(x))/h) -- 0 --> D"
by (simp add: deriv_def)

lemma DERIV_const [simp]: "DERIV (\<lambda>x. k) x :> 0"
  by (simp add: deriv_def tendsto_const)

lemma DERIV_ident [simp]: "DERIV (\<lambda>x. x) x :> 1"
  by (simp add: deriv_def tendsto_const cong: LIM_cong)

lemma DERIV_add:
  "\<lbrakk>DERIV f x :> D; DERIV g x :> E\<rbrakk> \<Longrightarrow> DERIV (\<lambda>x. f x + g x) x :> D + E"
  by (simp only: deriv_def add_diff_add add_divide_distrib tendsto_add)

lemma DERIV_minus:
  "DERIV f x :> D \<Longrightarrow> DERIV (\<lambda>x. - f x) x :> - D"
  by (simp only: deriv_def minus_diff_minus divide_minus_left tendsto_minus)

lemma DERIV_diff:
  "\<lbrakk>DERIV f x :> D; DERIV g x :> E\<rbrakk> \<Longrightarrow> DERIV (\<lambda>x. f x - g x) x :> D - E"
by (simp only: diff_minus DERIV_add DERIV_minus)

lemma DERIV_add_minus:
  "\<lbrakk>DERIV f x :> D; DERIV g x :> E\<rbrakk> \<Longrightarrow> DERIV (\<lambda>x. f x + - g x) x :> D + - E"
by (simp only: DERIV_add DERIV_minus)

lemma DERIV_isCont: "DERIV f x :> D \<Longrightarrow> isCont f x"
proof (unfold isCont_iff)
  assume "DERIV f x :> D"
  hence "(\<lambda>h. (f(x+h) - f(x)) / h) -- 0 --> D"
    by (rule DERIV_D)
  hence "(\<lambda>h. (f(x+h) - f(x)) / h * h) -- 0 --> D * 0"
    by (intro tendsto_mult tendsto_ident_at)
  hence "(\<lambda>h. (f(x+h) - f(x)) * (h / h)) -- 0 --> 0"
    by simp
  hence "(\<lambda>h. f(x+h) - f(x)) -- 0 --> 0"
    by (simp cong: LIM_cong)
  thus "(\<lambda>h. f(x+h)) -- 0 --> f(x)"
    by (simp add: LIM_def dist_norm)
qed

lemma DERIV_mult_lemma:
  fixes a b c d :: "'a::real_field"
  shows "(a * b - c * d) / h = a * ((b - d) / h) + ((a - c) / h) * d"
by (simp add: diff_minus add_divide_distrib [symmetric] ring_distribs)

lemma DERIV_mult':
  assumes f: "DERIV f x :> D"
  assumes g: "DERIV g x :> E"
  shows "DERIV (\<lambda>x. f x * g x) x :> f x * E + D * g x"
proof (unfold deriv_def)
  from f have "isCont f x"
    by (rule DERIV_isCont)
  hence "(\<lambda>h. f(x+h)) -- 0 --> f x"
    by (simp only: isCont_iff)
  hence "(\<lambda>h. f(x+h) * ((g(x+h) - g x) / h) +
              ((f(x+h) - f x) / h) * g x)
          -- 0 --> f x * E + D * g x"
    by (intro tendsto_intros DERIV_D f g)
  thus "(\<lambda>h. (f(x+h) * g(x+h) - f x * g x) / h)
         -- 0 --> f x * E + D * g x"
    by (simp only: DERIV_mult_lemma)
qed

lemma DERIV_mult:
     "[| DERIV f x :> Da; DERIV g x :> Db |]
      ==> DERIV (%x. f x * g x) x :> (Da * g(x)) + (Db * f(x))"
by (drule (1) DERIV_mult', simp only: mult_commute add_commute)

lemma DERIV_unique:
      "[| DERIV f x :> D; DERIV f x :> E |] ==> D = E"
apply (simp add: deriv_def)
apply (blast intro: LIM_unique)
done

text{*Differentiation of finite sum*}

lemma DERIV_setsum:
  assumes "finite S"
  and "\<And> n. n \<in> S \<Longrightarrow> DERIV (%x. f x n) x :> (f' x n)"
  shows "DERIV (%x. setsum (f x) S) x :> setsum (f' x) S"
  using assms by induct (auto intro!: DERIV_add)

lemma DERIV_sumr [rule_format (no_asm)]:
     "(\<forall>r. m \<le> r & r < (m + n) --> DERIV (%x. f r x) x :> (f' r x))
      --> DERIV (%x. \<Sum>n=m..<n::nat. f n x :: real) x :> (\<Sum>r=m..<n. f' r x)"
  by (auto intro: DERIV_setsum)

text{*Alternative definition for differentiability*}

lemma DERIV_LIM_iff:
  fixes f :: "'a::{real_normed_vector,inverse} \<Rightarrow> 'a" shows
     "((%h. (f(a + h) - f(a)) / h) -- 0 --> D) =
      ((%x. (f(x)-f(a)) / (x-a)) -- a --> D)"
apply (rule iffI)
apply (drule_tac k="- a" in LIM_offset)
apply (simp add: diff_minus)
apply (drule_tac k="a" in LIM_offset)
apply (simp add: add_commute)
done

lemma DERIV_iff2: "(DERIV f x :> D) = ((%z. (f(z) - f(x)) / (z-x)) -- x --> D)"
by (simp add: deriv_def diff_minus [symmetric] DERIV_LIM_iff)

lemma DERIV_inverse_lemma:
  "\<lbrakk>a \<noteq> 0; b \<noteq> (0::'a::real_normed_field)\<rbrakk>
   \<Longrightarrow> (inverse a - inverse b) / h
     = - (inverse a * ((a - b) / h) * inverse b)"
by (simp add: inverse_diff_inverse)

lemma DERIV_inverse':
  assumes der: "DERIV f x :> D"
  assumes neq: "f x \<noteq> 0"
  shows "DERIV (\<lambda>x. inverse (f x)) x :> - (inverse (f x) * D * inverse (f x))"
    (is "DERIV _ _ :> ?E")
proof (unfold DERIV_iff2)
  from der have lim_f: "f -- x --> f x"
    by (rule DERIV_isCont [unfolded isCont_def])

  from neq have "0 < norm (f x)" by simp
  with LIM_D [OF lim_f] obtain s
    where s: "0 < s"
    and less_fx: "\<And>z. \<lbrakk>z \<noteq> x; norm (z - x) < s\<rbrakk>
                  \<Longrightarrow> norm (f z - f x) < norm (f x)"
    by fast

  show "(\<lambda>z. (inverse (f z) - inverse (f x)) / (z - x)) -- x --> ?E"
  proof (rule LIM_equal2 [OF s])
    fix z
    assume "z \<noteq> x" "norm (z - x) < s"
    hence "norm (f z - f x) < norm (f x)" by (rule less_fx)
    hence "f z \<noteq> 0" by auto
    thus "(inverse (f z) - inverse (f x)) / (z - x) =
          - (inverse (f z) * ((f z - f x) / (z - x)) * inverse (f x))"
      using neq by (rule DERIV_inverse_lemma)
  next
    from der have "(\<lambda>z. (f z - f x) / (z - x)) -- x --> D"
      by (unfold DERIV_iff2)
    thus "(\<lambda>z. - (inverse (f z) * ((f z - f x) / (z - x)) * inverse (f x)))
          -- x --> ?E"
      by (intro tendsto_intros lim_f neq)
  qed
qed

lemma DERIV_divide:
  "\<lbrakk>DERIV f x :> D; DERIV g x :> E; g x \<noteq> 0\<rbrakk>
   \<Longrightarrow> DERIV (\<lambda>x. f x / g x) x :> (D * g x - f x * E) / (g x * g x)"
apply (subgoal_tac "f x * - (inverse (g x) * E * inverse (g x)) +
          D * inverse (g x) = (D * g x - f x * E) / (g x * g x)")
apply (erule subst)
apply (unfold divide_inverse)
apply (erule DERIV_mult')
apply (erule (1) DERIV_inverse')
apply (simp add: ring_distribs nonzero_inverse_mult_distrib)
apply (simp add: mult_ac)
done

lemma DERIV_power_Suc:
  fixes f :: "'a \<Rightarrow> 'a::{real_normed_field}"
  assumes f: "DERIV f x :> D"
  shows "DERIV (\<lambda>x. f x ^ Suc n) x :> (1 + of_nat n) * (D * f x ^ n)"
proof (induct n)
case 0
  show ?case by (simp add: f)
case (Suc k)
  from DERIV_mult' [OF f Suc] show ?case
    apply (simp only: of_nat_Suc ring_distribs mult_1_left)
    apply (simp only: power_Suc algebra_simps)
    done
qed

lemma DERIV_power:
  fixes f :: "'a \<Rightarrow> 'a::{real_normed_field}"
  assumes f: "DERIV f x :> D"
  shows "DERIV (\<lambda>x. f x ^ n) x :> of_nat n * (D * f x ^ (n - Suc 0))"
by (cases "n", simp, simp add: DERIV_power_Suc f del: power_Suc)

text {* Caratheodory formulation of derivative at a point *}

lemma CARAT_DERIV:
     "(DERIV f x :> l) =
      (\<exists>g. (\<forall>z. f z - f x = g z * (z-x)) & isCont g x & g x = l)"
      (is "?lhs = ?rhs")
proof
  assume der: "DERIV f x :> l"
  show "\<exists>g. (\<forall>z. f z - f x = g z * (z-x)) \<and> isCont g x \<and> g x = l"
  proof (intro exI conjI)
    let ?g = "(%z. if z = x then l else (f z - f x) / (z-x))"
    show "\<forall>z. f z - f x = ?g z * (z-x)" by simp
    show "isCont ?g x" using der
      by (simp add: isCont_iff DERIV_iff diff_minus
               cong: LIM_equal [rule_format])
    show "?g x = l" by simp
  qed
next
  assume "?rhs"
  then obtain g where
    "(\<forall>z. f z - f x = g z * (z-x))" and "isCont g x" and "g x = l" by blast
  thus "(DERIV f x :> l)"
     by (auto simp add: isCont_iff DERIV_iff cong: LIM_cong)
qed

lemma DERIV_chain':
  assumes f: "DERIV f x :> D"
  assumes g: "DERIV g (f x) :> E"
  shows "DERIV (\<lambda>x. g (f x)) x :> E * D"
proof (unfold DERIV_iff2)
  obtain d where d: "\<forall>y. g y - g (f x) = d y * (y - f x)"
    and cont_d: "isCont d (f x)" and dfx: "d (f x) = E"
    using CARAT_DERIV [THEN iffD1, OF g] by fast
  from f have "f -- x --> f x"
    by (rule DERIV_isCont [unfolded isCont_def])
  with cont_d have "(\<lambda>z. d (f z)) -- x --> d (f x)"
    by (rule isCont_tendsto_compose)
  hence "(\<lambda>z. d (f z) * ((f z - f x) / (z - x)))
          -- x --> d (f x) * D"
    by (rule tendsto_mult [OF _ f [unfolded DERIV_iff2]])
  thus "(\<lambda>z. (g (f z) - g (f x)) / (z - x)) -- x --> E * D"
    by (simp add: d dfx)
qed

text {*
 Let's do the standard proof, though theorem
 @{text "LIM_mult2"} follows from a NS proof
*}

lemma DERIV_cmult:
      "DERIV f x :> D ==> DERIV (%x. c * f x) x :> c*D"
by (drule DERIV_mult' [OF DERIV_const], simp)

lemma DERIV_cdivide: "DERIV f x :> D ==> DERIV (%x. f x / c) x :> D / c"
  apply (subgoal_tac "DERIV (%x. (1 / c) * f x) x :> (1 / c) * D", force)
  apply (erule DERIV_cmult)
  done

text {* Standard version *}
lemma DERIV_chain: "[| DERIV f (g x) :> Da; DERIV g x :> Db |] ==> DERIV (f o g) x :> Da * Db"
by (drule (1) DERIV_chain', simp add: o_def mult_commute)

lemma DERIV_chain2: "[| DERIV f (g x) :> Da; DERIV g x :> Db |] ==> DERIV (%x. f (g x)) x :> Da * Db"
by (auto dest: DERIV_chain simp add: o_def)

text {* Derivative of linear multiplication *}
lemma DERIV_cmult_Id [simp]: "DERIV (op * c) x :> c"
by (cut_tac c = c and x = x in DERIV_ident [THEN DERIV_cmult], simp)

lemma DERIV_pow: "DERIV (%x. x ^ n) x :> real n * (x ^ (n - Suc 0))"
apply (cut_tac DERIV_power [OF DERIV_ident])
apply (simp add: real_of_nat_def)
done

text {* Power of @{text "-1"} *}

lemma DERIV_inverse:
  fixes x :: "'a::{real_normed_field}"
  shows "x \<noteq> 0 ==> DERIV (%x. inverse(x)) x :> (-(inverse x ^ Suc (Suc 0)))"
by (drule DERIV_inverse' [OF DERIV_ident]) simp

text {* Derivative of inverse *}
lemma DERIV_inverse_fun:
  fixes x :: "'a::{real_normed_field}"
  shows "[| DERIV f x :> d; f(x) \<noteq> 0 |]
      ==> DERIV (%x. inverse(f x)) x :> (- (d * inverse(f(x) ^ Suc (Suc 0))))"
by (drule (1) DERIV_inverse') (simp add: mult_ac nonzero_inverse_mult_distrib)

text {* Derivative of quotient *}
lemma DERIV_quotient:
  fixes x :: "'a::{real_normed_field}"
  shows "[| DERIV f x :> d; DERIV g x :> e; g(x) \<noteq> 0 |]
       ==> DERIV (%y. f(y) / (g y)) x :> (d*g(x) - (e*f(x))) / (g(x) ^ Suc (Suc 0))"
by (drule (2) DERIV_divide) (simp add: mult_commute)

text {* @{text "DERIV_intros"} *}
ML {*
structure Deriv_Intros = Named_Thms
(
  val name = @{binding DERIV_intros}
  val description = "DERIV introduction rules"
)
*}

setup Deriv_Intros.setup

lemma DERIV_cong: "\<lbrakk> DERIV f x :> X ; X = Y \<rbrakk> \<Longrightarrow> DERIV f x :> Y"
  by simp

declare
  DERIV_const[THEN DERIV_cong, DERIV_intros]
  DERIV_ident[THEN DERIV_cong, DERIV_intros]
  DERIV_add[THEN DERIV_cong, DERIV_intros]
  DERIV_minus[THEN DERIV_cong, DERIV_intros]
  DERIV_mult[THEN DERIV_cong, DERIV_intros]
  DERIV_diff[THEN DERIV_cong, DERIV_intros]
  DERIV_inverse'[THEN DERIV_cong, DERIV_intros]
  DERIV_divide[THEN DERIV_cong, DERIV_intros]
  DERIV_power[where 'a=real, THEN DERIV_cong,
              unfolded real_of_nat_def[symmetric], DERIV_intros]
  DERIV_setsum[THEN DERIV_cong, DERIV_intros]


subsection {* Differentiability predicate *}

definition
  differentiable :: "['a::real_normed_field \<Rightarrow> 'a, 'a] \<Rightarrow> bool"
    (infixl "differentiable" 60) where
  "f differentiable x = (\<exists>D. DERIV f x :> D)"

lemma differentiableE [elim?]:
  assumes "f differentiable x"
  obtains df where "DERIV f x :> df"
  using assms unfolding differentiable_def ..

lemma differentiableD: "f differentiable x ==> \<exists>D. DERIV f x :> D"
by (simp add: differentiable_def)

lemma differentiableI: "DERIV f x :> D ==> f differentiable x"
by (force simp add: differentiable_def)

lemma differentiable_ident [simp]: "(\<lambda>x. x) differentiable x"
  by (rule DERIV_ident [THEN differentiableI])

lemma differentiable_const [simp]: "(\<lambda>z. a) differentiable x"
  by (rule DERIV_const [THEN differentiableI])

lemma differentiable_compose:
  assumes f: "f differentiable (g x)"
  assumes g: "g differentiable x"
  shows "(\<lambda>x. f (g x)) differentiable x"
proof -
  from `f differentiable (g x)` obtain df where "DERIV f (g x) :> df" ..
  moreover
  from `g differentiable x` obtain dg where "DERIV g x :> dg" ..
  ultimately
  have "DERIV (\<lambda>x. f (g x)) x :> df * dg" by (rule DERIV_chain2)
  thus ?thesis by (rule differentiableI)
qed

lemma differentiable_sum [simp]:
  assumes "f differentiable x"
  and "g differentiable x"
  shows "(\<lambda>x. f x + g x) differentiable x"
proof -
  from `f differentiable x` obtain df where "DERIV f x :> df" ..
  moreover
  from `g differentiable x` obtain dg where "DERIV g x :> dg" ..
  ultimately
  have "DERIV (\<lambda>x. f x + g x) x :> df + dg" by (rule DERIV_add)
  thus ?thesis by (rule differentiableI)
qed

lemma differentiable_minus [simp]:
  assumes "f differentiable x"
  shows "(\<lambda>x. - f x) differentiable x"
proof -
  from `f differentiable x` obtain df where "DERIV f x :> df" ..
  hence "DERIV (\<lambda>x. - f x) x :> - df" by (rule DERIV_minus)
  thus ?thesis by (rule differentiableI)
qed

lemma differentiable_diff [simp]:
  assumes "f differentiable x"
  assumes "g differentiable x"
  shows "(\<lambda>x. f x - g x) differentiable x"
  unfolding diff_minus using assms by simp

lemma differentiable_mult [simp]:
  assumes "f differentiable x"
  assumes "g differentiable x"
  shows "(\<lambda>x. f x * g x) differentiable x"
proof -
  from `f differentiable x` obtain df where "DERIV f x :> df" ..
  moreover
  from `g differentiable x` obtain dg where "DERIV g x :> dg" ..
  ultimately
  have "DERIV (\<lambda>x. f x * g x) x :> df * g x + dg * f x" by (rule DERIV_mult)
  thus ?thesis by (rule differentiableI)
qed

lemma differentiable_inverse [simp]:
  assumes "f differentiable x" and "f x \<noteq> 0"
  shows "(\<lambda>x. inverse (f x)) differentiable x"
proof -
  from `f differentiable x` obtain df where "DERIV f x :> df" ..
  hence "DERIV (\<lambda>x. inverse (f x)) x :> - (inverse (f x) * df * inverse (f x))"
    using `f x \<noteq> 0` by (rule DERIV_inverse')
  thus ?thesis by (rule differentiableI)
qed

lemma differentiable_divide [simp]:
  assumes "f differentiable x"
  assumes "g differentiable x" and "g x \<noteq> 0"
  shows "(\<lambda>x. f x / g x) differentiable x"
  unfolding divide_inverse using assms by simp

lemma differentiable_power [simp]:
  fixes f :: "'a::{real_normed_field} \<Rightarrow> 'a"
  assumes "f differentiable x"
  shows "(\<lambda>x. f x ^ n) differentiable x"
  apply (induct n)
  apply simp
  apply (simp add: assms)
  done


subsection {* Nested Intervals and Bisection *}

text{*Lemmas about nested intervals and proof by bisection (cf.Harrison).
     All considerably tidied by lcp.*}

lemma lemma_f_mono_add [rule_format (no_asm)]: "(\<forall>n. (f::nat=>real) n \<le> f (Suc n)) --> f m \<le> f(m + no)"
apply (induct "no")
apply (auto intro: order_trans)
done

lemma f_inc_g_dec_Beq_f: "[| \<forall>n. f(n) \<le> f(Suc n);
         \<forall>n. g(Suc n) \<le> g(n);
         \<forall>n. f(n) \<le> g(n) |]
      ==> Bseq (f :: nat \<Rightarrow> real)"
apply (rule_tac k = "f 0" and K = "g 0" in BseqI2, rule allI)
apply (rule conjI)
apply (induct_tac "n")
apply (auto intro: order_trans)
apply (rule_tac y = "g n" in order_trans)
apply (induct_tac [2] "n")
apply (auto intro: order_trans)
done

lemma f_inc_g_dec_Beq_g: "[| \<forall>n. f(n) \<le> f(Suc n);
         \<forall>n. g(Suc n) \<le> g(n);
         \<forall>n. f(n) \<le> g(n) |]
      ==> Bseq (g :: nat \<Rightarrow> real)"
apply (subst Bseq_minus_iff [symmetric])
apply (rule_tac g = "%x. - (f x)" in f_inc_g_dec_Beq_f)
apply auto
done

lemma f_inc_imp_le_lim:
  fixes f :: "nat \<Rightarrow> real"
  shows "\<lbrakk>\<forall>n. f n \<le> f (Suc n); convergent f\<rbrakk> \<Longrightarrow> f n \<le> lim f"
  by (rule incseq_le, simp add: incseq_SucI, simp add: convergent_LIMSEQ_iff)

lemma lim_uminus:
  fixes g :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "convergent g ==> lim (%x. - g x) = - (lim g)"
apply (rule tendsto_minus [THEN limI])
apply (simp add: convergent_LIMSEQ_iff)
done

lemma g_dec_imp_lim_le:
  fixes g :: "nat \<Rightarrow> real"
  shows "\<lbrakk>\<forall>n. g (Suc n) \<le> g(n); convergent g\<rbrakk> \<Longrightarrow> lim g \<le> g n"
  by (rule decseq_le, simp add: decseq_SucI, simp add: convergent_LIMSEQ_iff)

lemma lemma_nest: "[| \<forall>n. f(n) \<le> f(Suc n);
         \<forall>n. g(Suc n) \<le> g(n);
         \<forall>n. f(n) \<le> g(n) |]
      ==> \<exists>l m :: real. l \<le> m &  ((\<forall>n. f(n) \<le> l) & f ----> l) &
                            ((\<forall>n. m \<le> g(n)) & g ----> m)"
apply (subgoal_tac "monoseq f & monoseq g")
prefer 2 apply (force simp add: LIMSEQ_iff monoseq_Suc)
apply (subgoal_tac "Bseq f & Bseq g")
prefer 2 apply (blast intro: f_inc_g_dec_Beq_f f_inc_g_dec_Beq_g)
apply (auto dest!: Bseq_monoseq_convergent simp add: convergent_LIMSEQ_iff)
apply (rule_tac x = "lim f" in exI)
apply (rule_tac x = "lim g" in exI)
apply (auto intro: LIMSEQ_le)
apply (auto simp add: f_inc_imp_le_lim g_dec_imp_lim_le convergent_LIMSEQ_iff)
done

lemma lemma_nest_unique: "[| \<forall>n. f(n) \<le> f(Suc n);
         \<forall>n. g(Suc n) \<le> g(n);
         \<forall>n. f(n) \<le> g(n);
         (%n. f(n) - g(n)) ----> 0 |]
      ==> \<exists>l::real. ((\<forall>n. f(n) \<le> l) & f ----> l) &
                ((\<forall>n. l \<le> g(n)) & g ----> l)"
apply (drule lemma_nest, auto)
apply (subgoal_tac "l = m")
apply (drule_tac [2] f = f in tendsto_diff)
apply (auto intro: LIMSEQ_unique)
done

text{*The universal quantifiers below are required for the declaration
  of @{text Bolzano_nest_unique} below.*}

lemma Bolzano_bisect_le:
 "a \<le> b ==> \<forall>n. fst (Bolzano_bisect P a b n) \<le> snd (Bolzano_bisect P a b n)"
apply (rule allI)
apply (induct_tac "n")
apply (auto simp add: Let_def split_def)
done

lemma Bolzano_bisect_fst_le_Suc: "a \<le> b ==>
   \<forall>n. fst(Bolzano_bisect P a b n) \<le> fst (Bolzano_bisect P a b (Suc n))"
apply (rule allI)
apply (induct_tac "n")
apply (auto simp add: Bolzano_bisect_le Let_def split_def)
done

lemma Bolzano_bisect_Suc_le_snd: "a \<le> b ==>
   \<forall>n. snd(Bolzano_bisect P a b (Suc n)) \<le> snd (Bolzano_bisect P a b n)"
apply (rule allI)
apply (induct_tac "n")
apply (auto simp add: Bolzano_bisect_le Let_def split_def)
done

lemma eq_divide_2_times_iff: "((x::real) = y / (2 * z)) = (2 * x = y/z)"
apply (auto)
apply (drule_tac f = "%u. (1/2) *u" in arg_cong)
apply (simp)
done

lemma Bolzano_bisect_diff:
     "a \<le> b ==>
      snd(Bolzano_bisect P a b n) - fst(Bolzano_bisect P a b n) =
      (b-a) / (2 ^ n)"
apply (induct "n")
apply (auto simp add: eq_divide_2_times_iff add_divide_distrib Let_def split_def)
done

lemmas Bolzano_nest_unique =
    lemma_nest_unique
    [OF Bolzano_bisect_fst_le_Suc Bolzano_bisect_Suc_le_snd Bolzano_bisect_le]


lemma not_P_Bolzano_bisect:
  assumes P:    "!!a b c. [| P(a,b); P(b,c); a \<le> b; b \<le> c|] ==> P(a,c)"
      and notP: "~ P(a,b)"
      and le:   "a \<le> b"
  shows "~ P(fst(Bolzano_bisect P a b n), snd(Bolzano_bisect P a b n))"
proof (induct n)
  case 0 show ?case using notP by simp
 next
  case (Suc n)
  thus ?case
 by (auto simp del: surjective_pairing [symmetric]
             simp add: Let_def split_def Bolzano_bisect_le [OF le]
     P [of "fst (Bolzano_bisect P a b n)" _ "snd (Bolzano_bisect P a b n)"])
qed

(*Now we re-package P_prem as a formula*)
lemma not_P_Bolzano_bisect':
     "[| \<forall>a b c. P(a,b) & P(b,c) & a \<le> b & b \<le> c --> P(a,c);
         ~ P(a,b);  a \<le> b |] ==>
      \<forall>n. ~ P(fst(Bolzano_bisect P a b n), snd(Bolzano_bisect P a b n))"
by (blast elim!: not_P_Bolzano_bisect [THEN [2] rev_notE])



lemma lemma_BOLZANO:
     "[| \<forall>a b c. P(a,b) & P(b,c) & a \<le> b & b \<le> c --> P(a,c);
         \<forall>x. \<exists>d::real. 0 < d &
                (\<forall>a b. a \<le> x & x \<le> b & (b-a) < d --> P(a,b));
         a \<le> b |]
      ==> P(a,b)"
apply (rule Bolzano_nest_unique [where P1=P, THEN exE], assumption+)
apply (rule tendsto_minus_cancel)
apply (simp (no_asm_simp) add: Bolzano_bisect_diff LIMSEQ_divide_realpow_zero)
apply (rule ccontr)
apply (drule not_P_Bolzano_bisect', assumption+)
apply (rename_tac "l")
apply (drule_tac x = l in spec, clarify)
apply (simp add: LIMSEQ_iff)
apply (drule_tac P = "%r. 0<r --> ?Q r" and x = "d/2" in spec)
apply (drule_tac P = "%r. 0<r --> ?Q r" and x = "d/2" in spec)
apply (drule real_less_half_sum, auto)
apply (drule_tac x = "fst (Bolzano_bisect P a b (no + noa))" in spec)
apply (drule_tac x = "snd (Bolzano_bisect P a b (no + noa))" in spec)
apply safe
apply (simp_all (no_asm_simp))
apply (rule_tac y = "abs (fst (Bolzano_bisect P a b (no + noa)) - l) + abs (snd (Bolzano_bisect P a b (no + noa)) - l)" in order_le_less_trans)
apply (simp (no_asm_simp) add: abs_if)
apply (rule real_sum_of_halves [THEN subst])
apply (rule add_strict_mono)
apply (simp_all add: diff_minus [symmetric])
done


lemma lemma_BOLZANO2: "((\<forall>a b c. (a \<le> b & b \<le> c & P(a,b) & P(b,c)) --> P(a,c)) &
       (\<forall>x. \<exists>d::real. 0 < d &
                (\<forall>a b. a \<le> x & x \<le> b & (b-a) < d --> P(a,b))))
      --> (\<forall>a b. a \<le> b --> P(a,b))"
apply clarify
apply (blast intro: lemma_BOLZANO)
done


subsection {* Intermediate Value Theorem *}

text {*Prove Contrapositive by Bisection*}

lemma IVT: "[| f(a::real) \<le> (y::real); y \<le> f(b);
         a \<le> b;
         (\<forall>x. a \<le> x & x \<le> b --> isCont f x) |]
      ==> \<exists>x. a \<le> x & x \<le> b & f(x) = y"
apply (rule contrapos_pp, assumption)
apply (cut_tac P = "% (u,v) . a \<le> u & u \<le> v & v \<le> b --> ~ (f (u) \<le> y & y \<le> f (v))" in lemma_BOLZANO2)
apply safe
apply simp_all
apply (simp add: isCont_iff LIM_eq)
apply (rule ccontr)
apply (subgoal_tac "a \<le> x & x \<le> b")
 prefer 2
 apply simp
 apply (drule_tac P = "%d. 0<d --> ?P d" and x = 1 in spec, arith)
apply (drule_tac x = x in spec)+
apply simp
apply (drule_tac P = "%r. ?P r --> (\<exists>s>0. ?Q r s) " and x = "\<bar>y - f x\<bar>" in spec)
apply safe
apply simp
apply (drule_tac x = s in spec, clarify)
apply (cut_tac x = "f x" and y = y in linorder_less_linear, safe)
apply (drule_tac x = "ba-x" in spec)
apply (simp_all add: abs_if)
apply (drule_tac x = "aa-x" in spec)
apply (case_tac "x \<le> aa", simp_all)
done

lemma IVT2: "[| f(b::real) \<le> (y::real); y \<le> f(a);
         a \<le> b;
         (\<forall>x. a \<le> x & x \<le> b --> isCont f x)
      |] ==> \<exists>x. a \<le> x & x \<le> b & f(x) = y"
apply (subgoal_tac "- f a \<le> -y & -y \<le> - f b", clarify)
apply (drule IVT [where f = "%x. - f x"], assumption)
apply simp_all
done

(*HOL style here: object-level formulations*)
lemma IVT_objl: "(f(a::real) \<le> (y::real) & y \<le> f(b) & a \<le> b &
      (\<forall>x. a \<le> x & x \<le> b --> isCont f x))
      --> (\<exists>x. a \<le> x & x \<le> b & f(x) = y)"
apply (blast intro: IVT)
done

lemma IVT2_objl: "(f(b::real) \<le> (y::real) & y \<le> f(a) & a \<le> b &
      (\<forall>x. a \<le> x & x \<le> b --> isCont f x))
      --> (\<exists>x. a \<le> x & x \<le> b & f(x) = y)"
apply (blast intro: IVT2)
done


subsection {* Boundedness of continuous functions *}

text{*By bisection, function continuous on closed interval is bounded above*}

lemma isCont_bounded:
     "[| a \<le> b; \<forall>x. a \<le> x & x \<le> b --> isCont f x |]
      ==> \<exists>M::real. \<forall>x::real. a \<le> x & x \<le> b --> f(x) \<le> M"
apply (cut_tac P = "% (u,v) . a \<le> u & u \<le> v & v \<le> b --> (\<exists>M. \<forall>x. u \<le> x & x \<le> v --> f x \<le> M)" in lemma_BOLZANO2)
apply safe
apply simp_all
apply (rename_tac x xa ya M Ma)
apply (metis linorder_not_less order_le_less order_trans)
apply (case_tac "a \<le> x & x \<le> b")
 prefer 2
 apply (rule_tac x = 1 in exI, force)
apply (simp add: LIM_eq isCont_iff)
apply (drule_tac x = x in spec, auto)
apply (erule_tac V = "\<forall>M. \<exists>x. a \<le> x & x \<le> b & ~ f x \<le> M" in thin_rl)
apply (drule_tac x = 1 in spec, auto)
apply (rule_tac x = s in exI, clarify)
apply (rule_tac x = "\<bar>f x\<bar> + 1" in exI, clarify)
apply (drule_tac x = "xa-x" in spec)
apply (auto simp add: abs_ge_self)
done

text{*Refine the above to existence of least upper bound*}

lemma lemma_reals_complete: "((\<exists>x. x \<in> S) & (\<exists>y. isUb UNIV S (y::real))) -->
      (\<exists>t. isLub UNIV S t)"
by (blast intro: reals_complete)

lemma isCont_has_Ub: "[| a \<le> b; \<forall>x. a \<le> x & x \<le> b --> isCont f x |]
         ==> \<exists>M::real. (\<forall>x::real. a \<le> x & x \<le> b --> f(x) \<le> M) &
                   (\<forall>N. N < M --> (\<exists>x. a \<le> x & x \<le> b & N < f(x)))"
apply (cut_tac S = "Collect (%y. \<exists>x. a \<le> x & x \<le> b & y = f x)"
        in lemma_reals_complete)
apply auto
apply (drule isCont_bounded, assumption)
apply (auto simp add: isUb_def leastP_def isLub_def setge_def setle_def)
apply (rule exI, auto)
apply (auto dest!: spec simp add: linorder_not_less)
done

text{*Now show that it attains its upper bound*}

lemma isCont_eq_Ub:
  assumes le: "a \<le> b"
      and con: "\<forall>x::real. a \<le> x & x \<le> b --> isCont f x"
  shows "\<exists>M::real. (\<forall>x. a \<le> x & x \<le> b --> f(x) \<le> M) &
             (\<exists>x. a \<le> x & x \<le> b & f(x) = M)"
proof -
  from isCont_has_Ub [OF le con]
  obtain M where M1: "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f x \<le> M"
             and M2: "!!N. N<M ==> \<exists>x. a \<le> x \<and> x \<le> b \<and> N < f x"  by blast
  show ?thesis
  proof (intro exI, intro conjI)
    show " \<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f x \<le> M" by (rule M1)
    show "\<exists>x. a \<le> x \<and> x \<le> b \<and> f x = M"
    proof (rule ccontr)
      assume "\<not> (\<exists>x. a \<le> x \<and> x \<le> b \<and> f x = M)"
      with M1 have M3: "\<forall>x. a \<le> x & x \<le> b --> f x < M"
        by (fastforce simp add: linorder_not_le [symmetric])
      hence "\<forall>x. a \<le> x & x \<le> b --> isCont (%x. inverse (M - f x)) x"
        by (auto simp add: con)
      from isCont_bounded [OF le this]
      obtain k where k: "!!x. a \<le> x & x \<le> b --> inverse (M - f x) \<le> k" by auto
      have Minv: "!!x. a \<le> x & x \<le> b --> 0 < inverse (M - f (x))"
        by (simp add: M3 algebra_simps)
      have "!!x. a \<le> x & x \<le> b --> inverse (M - f x) < k+1" using k
        by (auto intro: order_le_less_trans [of _ k])
      with Minv
      have "!!x. a \<le> x & x \<le> b --> inverse(k+1) < inverse(inverse(M - f x))"
        by (intro strip less_imp_inverse_less, simp_all)
      hence invlt: "!!x. a \<le> x & x \<le> b --> inverse(k+1) < M - f x"
        by simp
      have "M - inverse (k+1) < M" using k [of a] Minv [of a] le
        by (simp, arith)
      from M2 [OF this]
      obtain x where ax: "a \<le> x & x \<le> b & M - inverse(k+1) < f x" ..
      thus False using invlt [of x] by force
    qed
  qed
qed


text{*Same theorem for lower bound*}

lemma isCont_eq_Lb: "[| a \<le> b; \<forall>x. a \<le> x & x \<le> b --> isCont f x |]
         ==> \<exists>M::real. (\<forall>x::real. a \<le> x & x \<le> b --> M \<le> f(x)) &
                   (\<exists>x. a \<le> x & x \<le> b & f(x) = M)"
apply (subgoal_tac "\<forall>x. a \<le> x & x \<le> b --> isCont (%x. - (f x)) x")
prefer 2 apply (blast intro: isCont_minus)
apply (drule_tac f = "(%x. - (f x))" in isCont_eq_Ub)
apply safe
apply auto
done


text{*Another version.*}

lemma isCont_Lb_Ub: "[|a \<le> b; \<forall>x. a \<le> x & x \<le> b --> isCont f x |]
      ==> \<exists>L M::real. (\<forall>x::real. a \<le> x & x \<le> b --> L \<le> f(x) & f(x) \<le> M) &
          (\<forall>y. L \<le> y & y \<le> M --> (\<exists>x. a \<le> x & x \<le> b & (f(x) = y)))"
apply (frule isCont_eq_Lb)
apply (frule_tac [2] isCont_eq_Ub)
apply (assumption+, safe)
apply (rule_tac x = "f x" in exI)
apply (rule_tac x = "f xa" in exI, simp, safe)
apply (cut_tac x = x and y = xa in linorder_linear, safe)
apply (cut_tac f = f and a = x and b = xa and y = y in IVT_objl)
apply (cut_tac [2] f = f and a = xa and b = x and y = y in IVT2_objl, safe)
apply (rule_tac [2] x = xb in exI)
apply (rule_tac [4] x = xb in exI, simp_all)
done


subsection {* Local extrema *}

text{*If @{term "0 < f'(x)"} then @{term x} is Locally Strictly Increasing At The Right*}

lemma DERIV_pos_inc_right:
  fixes f :: "real => real"
  assumes der: "DERIV f x :> l"
      and l:   "0 < l"
  shows "\<exists>d > 0. \<forall>h > 0. h < d --> f(x) < f(x + h)"
proof -
  from l der [THEN DERIV_D, THEN LIM_D [where r = "l"]]
  have "\<exists>s > 0. (\<forall>z. z \<noteq> 0 \<and> \<bar>z\<bar> < s \<longrightarrow> \<bar>(f(x+z) - f x) / z - l\<bar> < l)"
    by (simp add: diff_minus)
  then obtain s
        where s:   "0 < s"
          and all: "!!z. z \<noteq> 0 \<and> \<bar>z\<bar> < s \<longrightarrow> \<bar>(f(x+z) - f x) / z - l\<bar> < l"
    by auto
  thus ?thesis
  proof (intro exI conjI strip)
    show "0<s" using s .
    fix h::real
    assume "0 < h" "h < s"
    with all [of h] show "f x < f (x+h)"
    proof (simp add: abs_if pos_less_divide_eq diff_minus [symmetric]
    split add: split_if_asm)
      assume "~ (f (x+h) - f x) / h < l" and h: "0 < h"
      with l
      have "0 < (f (x+h) - f x) / h" by arith
      thus "f x < f (x+h)"
  by (simp add: pos_less_divide_eq h)
    qed
  qed
qed

lemma DERIV_neg_dec_left:
  fixes f :: "real => real"
  assumes der: "DERIV f x :> l"
      and l:   "l < 0"
  shows "\<exists>d > 0. \<forall>h > 0. h < d --> f(x) < f(x-h)"
proof -
  from l der [THEN DERIV_D, THEN LIM_D [where r = "-l"]]
  have "\<exists>s > 0. (\<forall>z. z \<noteq> 0 \<and> \<bar>z\<bar> < s \<longrightarrow> \<bar>(f(x+z) - f x) / z - l\<bar> < -l)"
    by (simp add: diff_minus)
  then obtain s
        where s:   "0 < s"
          and all: "!!z. z \<noteq> 0 \<and> \<bar>z\<bar> < s \<longrightarrow> \<bar>(f(x+z) - f x) / z - l\<bar> < -l"
    by auto
  thus ?thesis
  proof (intro exI conjI strip)
    show "0<s" using s .
    fix h::real
    assume "0 < h" "h < s"
    with all [of "-h"] show "f x < f (x-h)"
    proof (simp add: abs_if pos_less_divide_eq diff_minus [symmetric]
    split add: split_if_asm)
      assume " - ((f (x-h) - f x) / h) < l" and h: "0 < h"
      with l
      have "0 < (f (x-h) - f x) / h" by arith
      thus "f x < f (x-h)"
  by (simp add: pos_less_divide_eq h)
    qed
  qed
qed


lemma DERIV_pos_inc_left:
  fixes f :: "real => real"
  shows "DERIV f x :> l \<Longrightarrow> 0 < l \<Longrightarrow> \<exists>d > 0. \<forall>h > 0. h < d --> f(x - h) < f(x)"
  apply (rule DERIV_neg_dec_left [of "%x. - f x" x "-l", simplified])
  apply (auto simp add: DERIV_minus)
  done

lemma DERIV_neg_dec_right:
  fixes f :: "real => real"
  shows "DERIV f x :> l \<Longrightarrow> l < 0 \<Longrightarrow> \<exists>d > 0. \<forall>h > 0. h < d --> f(x) > f(x + h)"
  apply (rule DERIV_pos_inc_right [of "%x. - f x" x "-l", simplified])
  apply (auto simp add: DERIV_minus)
  done

lemma DERIV_local_max:
  fixes f :: "real => real"
  assumes der: "DERIV f x :> l"
      and d:   "0 < d"
      and le:  "\<forall>y. \<bar>x-y\<bar> < d --> f(y) \<le> f(x)"
  shows "l = 0"
proof (cases rule: linorder_cases [of l 0])
  case equal thus ?thesis .
next
  case less
  from DERIV_neg_dec_left [OF der less]
  obtain d' where d': "0 < d'"
             and lt: "\<forall>h > 0. h < d' \<longrightarrow> f x < f (x-h)" by blast
  from real_lbound_gt_zero [OF d d']
  obtain e where "0 < e \<and> e < d \<and> e < d'" ..
  with lt le [THEN spec [where x="x-e"]]
  show ?thesis by (auto simp add: abs_if)
next
  case greater
  from DERIV_pos_inc_right [OF der greater]
  obtain d' where d': "0 < d'"
             and lt: "\<forall>h > 0. h < d' \<longrightarrow> f x < f (x + h)" by blast
  from real_lbound_gt_zero [OF d d']
  obtain e where "0 < e \<and> e < d \<and> e < d'" ..
  with lt le [THEN spec [where x="x+e"]]
  show ?thesis by (auto simp add: abs_if)
qed


text{*Similar theorem for a local minimum*}
lemma DERIV_local_min:
  fixes f :: "real => real"
  shows "[| DERIV f x :> l; 0 < d; \<forall>y. \<bar>x-y\<bar> < d --> f(x) \<le> f(y) |] ==> l = 0"
by (drule DERIV_minus [THEN DERIV_local_max], auto)


text{*In particular, if a function is locally flat*}
lemma DERIV_local_const:
  fixes f :: "real => real"
  shows "[| DERIV f x :> l; 0 < d; \<forall>y. \<bar>x-y\<bar> < d --> f(x) = f(y) |] ==> l = 0"
by (auto dest!: DERIV_local_max)


subsection {* Rolle's Theorem *}

text{*Lemma about introducing open ball in open interval*}
lemma lemma_interval_lt:
     "[| a < x;  x < b |]
      ==> \<exists>d::real. 0 < d & (\<forall>y. \<bar>x-y\<bar> < d --> a < y & y < b)"

apply (simp add: abs_less_iff)
apply (insert linorder_linear [of "x-a" "b-x"], safe)
apply (rule_tac x = "x-a" in exI)
apply (rule_tac [2] x = "b-x" in exI, auto)
done

lemma lemma_interval: "[| a < x;  x < b |] ==>
        \<exists>d::real. 0 < d &  (\<forall>y. \<bar>x-y\<bar> < d --> a \<le> y & y \<le> b)"
apply (drule lemma_interval_lt, auto)
apply force
done

text{*Rolle's Theorem.
   If @{term f} is defined and continuous on the closed interval
   @{text "[a,b]"} and differentiable on the open interval @{text "(a,b)"},
   and @{term "f(a) = f(b)"},
   then there exists @{text "x0 \<in> (a,b)"} such that @{term "f'(x0) = 0"}*}
theorem Rolle:
  assumes lt: "a < b"
      and eq: "f(a) = f(b)"
      and con: "\<forall>x. a \<le> x & x \<le> b --> isCont f x"
      and dif [rule_format]: "\<forall>x. a < x & x < b --> f differentiable x"
  shows "\<exists>z::real. a < z & z < b & DERIV f z :> 0"
proof -
  have le: "a \<le> b" using lt by simp
  from isCont_eq_Ub [OF le con]
  obtain x where x_max: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> f z \<le> f x"
             and alex: "a \<le> x" and xleb: "x \<le> b"
    by blast
  from isCont_eq_Lb [OF le con]
  obtain x' where x'_min: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> f x' \<le> f z"
              and alex': "a \<le> x'" and x'leb: "x' \<le> b"
    by blast
  show ?thesis
  proof cases
    assume axb: "a < x & x < b"
        --{*@{term f} attains its maximum within the interval*}
    hence ax: "a<x" and xb: "x<b" by arith + 
    from lemma_interval [OF ax xb]
    obtain d where d: "0<d" and bound: "\<forall>y. \<bar>x-y\<bar> < d \<longrightarrow> a \<le> y \<and> y \<le> b"
      by blast
    hence bound': "\<forall>y. \<bar>x-y\<bar> < d \<longrightarrow> f y \<le> f x" using x_max
      by blast
    from differentiableD [OF dif [OF axb]]
    obtain l where der: "DERIV f x :> l" ..
    have "l=0" by (rule DERIV_local_max [OF der d bound'])
        --{*the derivative at a local maximum is zero*}
    thus ?thesis using ax xb der by auto
  next
    assume notaxb: "~ (a < x & x < b)"
    hence xeqab: "x=a | x=b" using alex xleb by arith
    hence fb_eq_fx: "f b = f x" by (auto simp add: eq)
    show ?thesis
    proof cases
      assume ax'b: "a < x' & x' < b"
        --{*@{term f} attains its minimum within the interval*}
      hence ax': "a<x'" and x'b: "x'<b" by arith+ 
      from lemma_interval [OF ax' x'b]
      obtain d where d: "0<d" and bound: "\<forall>y. \<bar>x'-y\<bar> < d \<longrightarrow> a \<le> y \<and> y \<le> b"
  by blast
      hence bound': "\<forall>y. \<bar>x'-y\<bar> < d \<longrightarrow> f x' \<le> f y" using x'_min
  by blast
      from differentiableD [OF dif [OF ax'b]]
      obtain l where der: "DERIV f x' :> l" ..
      have "l=0" by (rule DERIV_local_min [OF der d bound'])
        --{*the derivative at a local minimum is zero*}
      thus ?thesis using ax' x'b der by auto
    next
      assume notax'b: "~ (a < x' & x' < b)"
        --{*@{term f} is constant througout the interval*}
      hence x'eqab: "x'=a | x'=b" using alex' x'leb by arith
      hence fb_eq_fx': "f b = f x'" by (auto simp add: eq)
      from dense [OF lt]
      obtain r where ar: "a < r" and rb: "r < b" by blast
      from lemma_interval [OF ar rb]
      obtain d where d: "0<d" and bound: "\<forall>y. \<bar>r-y\<bar> < d \<longrightarrow> a \<le> y \<and> y \<le> b"
  by blast
      have eq_fb: "\<forall>z. a \<le> z --> z \<le> b --> f z = f b"
      proof (clarify)
        fix z::real
        assume az: "a \<le> z" and zb: "z \<le> b"
        show "f z = f b"
        proof (rule order_antisym)
          show "f z \<le> f b" by (simp add: fb_eq_fx x_max az zb)
          show "f b \<le> f z" by (simp add: fb_eq_fx' x'_min az zb)
        qed
      qed
      have bound': "\<forall>y. \<bar>r-y\<bar> < d \<longrightarrow> f r = f y"
      proof (intro strip)
        fix y::real
        assume lt: "\<bar>r-y\<bar> < d"
        hence "f y = f b" by (simp add: eq_fb bound)
        thus "f r = f y" by (simp add: eq_fb ar rb order_less_imp_le)
      qed
      from differentiableD [OF dif [OF conjI [OF ar rb]]]
      obtain l where der: "DERIV f r :> l" ..
      have "l=0" by (rule DERIV_local_const [OF der d bound'])
        --{*the derivative of a constant function is zero*}
      thus ?thesis using ar rb der by auto
    qed
  qed
qed


subsection{*Mean Value Theorem*}

lemma lemma_MVT:
     "f a - (f b - f a)/(b-a) * a = f b - (f b - f a)/(b-a) * (b::real)"
proof cases
  assume "a=b" thus ?thesis by simp
next
  assume "a\<noteq>b"
  hence ba: "b-a \<noteq> 0" by arith
  show ?thesis
    by (rule real_mult_left_cancel [OF ba, THEN iffD1],
        simp add: right_diff_distrib,
        simp add: left_diff_distrib)
qed

theorem MVT:
  assumes lt:  "a < b"
      and con: "\<forall>x. a \<le> x & x \<le> b --> isCont f x"
      and dif [rule_format]: "\<forall>x. a < x & x < b --> f differentiable x"
  shows "\<exists>l z::real. a < z & z < b & DERIV f z :> l &
                   (f(b) - f(a) = (b-a) * l)"
proof -
  let ?F = "%x. f x - ((f b - f a) / (b-a)) * x"
  have contF: "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont ?F x"
    using con by (fast intro: isCont_intros)
  have difF: "\<forall>x. a < x \<and> x < b \<longrightarrow> ?F differentiable x"
  proof (clarify)
    fix x::real
    assume ax: "a < x" and xb: "x < b"
    from differentiableD [OF dif [OF conjI [OF ax xb]]]
    obtain l where der: "DERIV f x :> l" ..
    show "?F differentiable x"
      by (rule differentiableI [where D = "l - (f b - f a)/(b-a)"],
          blast intro: DERIV_diff DERIV_cmult_Id der)
  qed
  from Rolle [where f = ?F, OF lt lemma_MVT contF difF]
  obtain z where az: "a < z" and zb: "z < b" and der: "DERIV ?F z :> 0"
    by blast
  have "DERIV (%x. ((f b - f a)/(b-a)) * x) z :> (f b - f a)/(b-a)"
    by (rule DERIV_cmult_Id)
  hence derF: "DERIV (\<lambda>x. ?F x + (f b - f a) / (b - a) * x) z
                   :> 0 + (f b - f a) / (b - a)"
    by (rule DERIV_add [OF der])
  show ?thesis
  proof (intro exI conjI)
    show "a < z" using az .
    show "z < b" using zb .
    show "f b - f a = (b - a) * ((f b - f a)/(b-a))" by (simp)
    show "DERIV f z :> ((f b - f a)/(b-a))"  using derF by simp
  qed
qed

lemma MVT2:
     "[| a < b; \<forall>x. a \<le> x & x \<le> b --> DERIV f x :> f'(x) |]
      ==> \<exists>z::real. a < z & z < b & (f b - f a = (b - a) * f'(z))"
apply (drule MVT)
apply (blast intro: DERIV_isCont)
apply (force dest: order_less_imp_le simp add: differentiable_def)
apply (blast dest: DERIV_unique order_less_imp_le)
done


text{*A function is constant if its derivative is 0 over an interval.*}

lemma DERIV_isconst_end:
  fixes f :: "real => real"
  shows "[| a < b;
         \<forall>x. a \<le> x & x \<le> b --> isCont f x;
         \<forall>x. a < x & x < b --> DERIV f x :> 0 |]
        ==> f b = f a"
apply (drule MVT, assumption)
apply (blast intro: differentiableI)
apply (auto dest!: DERIV_unique simp add: diff_eq_eq)
done

lemma DERIV_isconst1:
  fixes f :: "real => real"
  shows "[| a < b;
         \<forall>x. a \<le> x & x \<le> b --> isCont f x;
         \<forall>x. a < x & x < b --> DERIV f x :> 0 |]
        ==> \<forall>x. a \<le> x & x \<le> b --> f x = f a"
apply safe
apply (drule_tac x = a in order_le_imp_less_or_eq, safe)
apply (drule_tac b = x in DERIV_isconst_end, auto)
done

lemma DERIV_isconst2:
  fixes f :: "real => real"
  shows "[| a < b;
         \<forall>x. a \<le> x & x \<le> b --> isCont f x;
         \<forall>x. a < x & x < b --> DERIV f x :> 0;
         a \<le> x; x \<le> b |]
        ==> f x = f a"
apply (blast dest: DERIV_isconst1)
done

lemma DERIV_isconst3: fixes a b x y :: real
  assumes "a < b" and "x \<in> {a <..< b}" and "y \<in> {a <..< b}"
  assumes derivable: "\<And>x. x \<in> {a <..< b} \<Longrightarrow> DERIV f x :> 0"
  shows "f x = f y"
proof (cases "x = y")
  case False
  let ?a = "min x y"
  let ?b = "max x y"
  
  have "\<forall>z. ?a \<le> z \<and> z \<le> ?b \<longrightarrow> DERIV f z :> 0"
  proof (rule allI, rule impI)
    fix z :: real assume "?a \<le> z \<and> z \<le> ?b"
    hence "a < z" and "z < b" using `x \<in> {a <..< b}` and `y \<in> {a <..< b}` by auto
    hence "z \<in> {a<..<b}" by auto
    thus "DERIV f z :> 0" by (rule derivable)
  qed
  hence isCont: "\<forall>z. ?a \<le> z \<and> z \<le> ?b \<longrightarrow> isCont f z"
    and DERIV: "\<forall>z. ?a < z \<and> z < ?b \<longrightarrow> DERIV f z :> 0" using DERIV_isCont by auto

  have "?a < ?b" using `x \<noteq> y` by auto
  from DERIV_isconst2[OF this isCont DERIV, of x] and DERIV_isconst2[OF this isCont DERIV, of y]
  show ?thesis by auto
qed auto

lemma DERIV_isconst_all:
  fixes f :: "real => real"
  shows "\<forall>x. DERIV f x :> 0 ==> f(x) = f(y)"
apply (rule linorder_cases [of x y])
apply (blast intro: sym DERIV_isCont DERIV_isconst_end)+
done

lemma DERIV_const_ratio_const:
  fixes f :: "real => real"
  shows "[|a \<noteq> b; \<forall>x. DERIV f x :> k |] ==> (f(b) - f(a)) = (b-a) * k"
apply (rule linorder_cases [of a b], auto)
apply (drule_tac [!] f = f in MVT)
apply (auto dest: DERIV_isCont DERIV_unique simp add: differentiable_def)
apply (auto dest: DERIV_unique simp add: ring_distribs diff_minus)
done

lemma DERIV_const_ratio_const2:
  fixes f :: "real => real"
  shows "[|a \<noteq> b; \<forall>x. DERIV f x :> k |] ==> (f(b) - f(a))/(b-a) = k"
apply (rule_tac c1 = "b-a" in real_mult_right_cancel [THEN iffD1])
apply (auto dest!: DERIV_const_ratio_const simp add: mult_assoc)
done

lemma real_average_minus_first [simp]: "((a + b) /2 - a) = (b-a)/(2::real)"
by (simp)

lemma real_average_minus_second [simp]: "((b + a)/2 - a) = (b-a)/(2::real)"
by (simp)

text{*Gallileo's "trick": average velocity = av. of end velocities*}

lemma DERIV_const_average:
  fixes v :: "real => real"
  assumes neq: "a \<noteq> (b::real)"
      and der: "\<forall>x. DERIV v x :> k"
  shows "v ((a + b)/2) = (v a + v b)/2"
proof (cases rule: linorder_cases [of a b])
  case equal with neq show ?thesis by simp
next
  case less
  have "(v b - v a) / (b - a) = k"
    by (rule DERIV_const_ratio_const2 [OF neq der])
  hence "(b-a) * ((v b - v a) / (b-a)) = (b-a) * k" by simp
  moreover have "(v ((a + b) / 2) - v a) / ((a + b) / 2 - a) = k"
    by (rule DERIV_const_ratio_const2 [OF _ der], simp add: neq)
  ultimately show ?thesis using neq by force
next
  case greater
  have "(v b - v a) / (b - a) = k"
    by (rule DERIV_const_ratio_const2 [OF neq der])
  hence "(b-a) * ((v b - v a) / (b-a)) = (b-a) * k" by simp
  moreover have " (v ((b + a) / 2) - v a) / ((b + a) / 2 - a) = k"
    by (rule DERIV_const_ratio_const2 [OF _ der], simp add: neq)
  ultimately show ?thesis using neq by (force simp add: add_commute)
qed

(* A function with positive derivative is increasing. 
   A simple proof using the MVT, by Jeremy Avigad. And variants.
*)
lemma DERIV_pos_imp_increasing:
  fixes a::real and b::real and f::"real => real"
  assumes "a < b" and "\<forall>x. a \<le> x & x \<le> b --> (EX y. DERIV f x :> y & y > 0)"
  shows "f a < f b"
proof (rule ccontr)
  assume f: "~ f a < f b"
  have "EX l z. a < z & z < b & DERIV f z :> l
      & f b - f a = (b - a) * l"
    apply (rule MVT)
      using assms
      apply auto
      apply (metis DERIV_isCont)
     apply (metis differentiableI less_le)
    done
  then obtain l z where z: "a < z" "z < b" "DERIV f z :> l"
      and "f b - f a = (b - a) * l"
    by auto
  with assms f have "~(l > 0)"
    by (metis linorder_not_le mult_le_0_iff diff_le_0_iff_le)
  with assms z show False
    by (metis DERIV_unique less_le)
qed

lemma DERIV_nonneg_imp_nonincreasing:
  fixes a::real and b::real and f::"real => real"
  assumes "a \<le> b" and
    "\<forall>x. a \<le> x & x \<le> b --> (\<exists>y. DERIV f x :> y & y \<ge> 0)"
  shows "f a \<le> f b"
proof (rule ccontr, cases "a = b")
  assume "~ f a \<le> f b" and "a = b"
  then show False by auto
next
  assume A: "~ f a \<le> f b"
  assume B: "a ~= b"
  with assms have "EX l z. a < z & z < b & DERIV f z :> l
      & f b - f a = (b - a) * l"
    apply -
    apply (rule MVT)
      apply auto
      apply (metis DERIV_isCont)
     apply (metis differentiableI less_le)
    done
  then obtain l z where z: "a < z" "z < b" "DERIV f z :> l"
      and C: "f b - f a = (b - a) * l"
    by auto
  with A have "a < b" "f b < f a" by auto
  with C have "\<not> l \<ge> 0" by (auto simp add: not_le algebra_simps)
    (metis A add_le_cancel_right assms(1) less_eq_real_def mult_right_mono add_left_mono linear order_refl)
  with assms z show False
    by (metis DERIV_unique order_less_imp_le)
qed

lemma DERIV_neg_imp_decreasing:
  fixes a::real and b::real and f::"real => real"
  assumes "a < b" and
    "\<forall>x. a \<le> x & x \<le> b --> (\<exists>y. DERIV f x :> y & y < 0)"
  shows "f a > f b"
proof -
  have "(%x. -f x) a < (%x. -f x) b"
    apply (rule DERIV_pos_imp_increasing [of a b "%x. -f x"])
    using assms
    apply auto
    apply (metis DERIV_minus neg_0_less_iff_less)
    done
  thus ?thesis
    by simp
qed

lemma DERIV_nonpos_imp_nonincreasing:
  fixes a::real and b::real and f::"real => real"
  assumes "a \<le> b" and
    "\<forall>x. a \<le> x & x \<le> b --> (\<exists>y. DERIV f x :> y & y \<le> 0)"
  shows "f a \<ge> f b"
proof -
  have "(%x. -f x) a \<le> (%x. -f x) b"
    apply (rule DERIV_nonneg_imp_nonincreasing [of a b "%x. -f x"])
    using assms
    apply auto
    apply (metis DERIV_minus neg_0_le_iff_le)
    done
  thus ?thesis
    by simp
qed

subsection {* Continuous injective functions *}

text{*Dull lemma: an continuous injection on an interval must have a
strict maximum at an end point, not in the middle.*}

lemma lemma_isCont_inj:
  fixes f :: "real \<Rightarrow> real"
  assumes d: "0 < d"
      and inj [rule_format]: "\<forall>z. \<bar>z-x\<bar> \<le> d --> g(f z) = z"
      and cont: "\<forall>z. \<bar>z-x\<bar> \<le> d --> isCont f z"
  shows "\<exists>z. \<bar>z-x\<bar> \<le> d & f x < f z"
proof (rule ccontr)
  assume  "~ (\<exists>z. \<bar>z-x\<bar> \<le> d & f x < f z)"
  hence all [rule_format]: "\<forall>z. \<bar>z - x\<bar> \<le> d --> f z \<le> f x" by auto
  show False
  proof (cases rule: linorder_le_cases [of "f(x-d)" "f(x+d)"])
    case le
    from d cont all [of "x+d"]
    have flef: "f(x+d) \<le> f x"
     and xlex: "x - d \<le> x"
     and cont': "\<forall>z. x - d \<le> z \<and> z \<le> x \<longrightarrow> isCont f z"
       by (auto simp add: abs_if)
    from IVT [OF le flef xlex cont']
    obtain x' where "x-d \<le> x'" "x' \<le> x" "f x' = f(x+d)" by blast
    moreover
    hence "g(f x') = g (f(x+d))" by simp
    ultimately show False using d inj [of x'] inj [of "x+d"]
      by (simp add: abs_le_iff)
  next
    case ge
    from d cont all [of "x-d"]
    have flef: "f(x-d) \<le> f x"
     and xlex: "x \<le> x+d"
     and cont': "\<forall>z. x \<le> z \<and> z \<le> x+d \<longrightarrow> isCont f z"
       by (auto simp add: abs_if)
    from IVT2 [OF ge flef xlex cont']
    obtain x' where "x \<le> x'" "x' \<le> x+d" "f x' = f(x-d)" by blast
    moreover
    hence "g(f x') = g (f(x-d))" by simp
    ultimately show False using d inj [of x'] inj [of "x-d"]
      by (simp add: abs_le_iff)
  qed
qed


text{*Similar version for lower bound.*}

lemma lemma_isCont_inj2:
  fixes f g :: "real \<Rightarrow> real"
  shows "[|0 < d; \<forall>z. \<bar>z-x\<bar> \<le> d --> g(f z) = z;
        \<forall>z. \<bar>z-x\<bar> \<le> d --> isCont f z |]
      ==> \<exists>z. \<bar>z-x\<bar> \<le> d & f z < f x"
apply (insert lemma_isCont_inj
          [where f = "%x. - f x" and g = "%y. g(-y)" and x = x and d = d])
apply (simp add: linorder_not_le)
done

text{*Show there's an interval surrounding @{term "f(x)"} in
@{text "f[[x - d, x + d]]"} .*}

lemma isCont_inj_range:
  fixes f :: "real \<Rightarrow> real"
  assumes d: "0 < d"
      and inj: "\<forall>z. \<bar>z-x\<bar> \<le> d --> g(f z) = z"
      and cont: "\<forall>z. \<bar>z-x\<bar> \<le> d --> isCont f z"
  shows "\<exists>e>0. \<forall>y. \<bar>y - f x\<bar> \<le> e --> (\<exists>z. \<bar>z-x\<bar> \<le> d & f z = y)"
proof -
  have "x-d \<le> x+d" "\<forall>z. x-d \<le> z \<and> z \<le> x+d \<longrightarrow> isCont f z" using cont d
    by (auto simp add: abs_le_iff)
  from isCont_Lb_Ub [OF this]
  obtain L M
  where all1 [rule_format]: "\<forall>z. x-d \<le> z \<and> z \<le> x+d \<longrightarrow> L \<le> f z \<and> f z \<le> M"
    and all2 [rule_format]:
           "\<forall>y. L \<le> y \<and> y \<le> M \<longrightarrow> (\<exists>z. x-d \<le> z \<and> z \<le> x+d \<and> f z = y)"
    by auto
  with d have "L \<le> f x & f x \<le> M" by simp
  moreover have "L \<noteq> f x"
  proof -
    from lemma_isCont_inj2 [OF d inj cont]
    obtain u where "\<bar>u - x\<bar> \<le> d" "f u < f x"  by auto
    thus ?thesis using all1 [of u] by arith
  qed
  moreover have "f x \<noteq> M"
  proof -
    from lemma_isCont_inj [OF d inj cont]
    obtain u where "\<bar>u - x\<bar> \<le> d" "f x < f u"  by auto
    thus ?thesis using all1 [of u] by arith
  qed
  ultimately have "L < f x & f x < M" by arith
  hence "0 < f x - L" "0 < M - f x" by arith+
  from real_lbound_gt_zero [OF this]
  obtain e where e: "0 < e" "e < f x - L" "e < M - f x" by auto
  thus ?thesis
  proof (intro exI conjI)
    show "0<e" using e(1) .
    show "\<forall>y. \<bar>y - f x\<bar> \<le> e \<longrightarrow> (\<exists>z. \<bar>z - x\<bar> \<le> d \<and> f z = y)"
    proof (intro strip)
      fix y::real
      assume "\<bar>y - f x\<bar> \<le> e"
      with e have "L \<le> y \<and> y \<le> M" by arith
      from all2 [OF this]
      obtain z where "x - d \<le> z" "z \<le> x + d" "f z = y" by blast
      thus "\<exists>z. \<bar>z - x\<bar> \<le> d \<and> f z = y" 
        by (force simp add: abs_le_iff)
    qed
  qed
qed


text{*Continuity of inverse function*}

lemma isCont_inverse_function:
  fixes f g :: "real \<Rightarrow> real"
  assumes d: "0 < d"
      and inj: "\<forall>z. \<bar>z-x\<bar> \<le> d --> g(f z) = z"
      and cont: "\<forall>z. \<bar>z-x\<bar> \<le> d --> isCont f z"
  shows "isCont g (f x)"
proof (simp add: isCont_iff LIM_eq)
  show "\<forall>r. 0 < r \<longrightarrow>
         (\<exists>s>0. \<forall>z. z\<noteq>0 \<and> \<bar>z\<bar> < s \<longrightarrow> \<bar>g(f x + z) - g(f x)\<bar> < r)"
  proof (intro strip)
    fix r::real
    assume r: "0<r"
    from real_lbound_gt_zero [OF r d]
    obtain e where e: "0 < e" and e_lt: "e < r \<and> e < d" by blast
    with inj cont
    have e_simps: "\<forall>z. \<bar>z-x\<bar> \<le> e --> g (f z) = z"
                  "\<forall>z. \<bar>z-x\<bar> \<le> e --> isCont f z"   by auto
    from isCont_inj_range [OF e this]
    obtain e' where e': "0 < e'"
        and all: "\<forall>y. \<bar>y - f x\<bar> \<le> e' \<longrightarrow> (\<exists>z. \<bar>z - x\<bar> \<le> e \<and> f z = y)"
          by blast
    show "\<exists>s>0. \<forall>z. z\<noteq>0 \<and> \<bar>z\<bar> < s \<longrightarrow> \<bar>g(f x + z) - g(f x)\<bar> < r"
    proof (intro exI conjI)
      show "0<e'" using e' .
      show "\<forall>z. z \<noteq> 0 \<and> \<bar>z\<bar> < e' \<longrightarrow> \<bar>g (f x + z) - g (f x)\<bar> < r"
      proof (intro strip)
        fix z::real
        assume z: "z \<noteq> 0 \<and> \<bar>z\<bar> < e'"
        with e e_lt e_simps all [rule_format, of "f x + z"]
        show "\<bar>g (f x + z) - g (f x)\<bar> < r" by force
      qed
    qed
  qed
qed

text {* Derivative of inverse function *}

lemma DERIV_inverse_function:
  fixes f g :: "real \<Rightarrow> real"
  assumes der: "DERIV f (g x) :> D"
  assumes neq: "D \<noteq> 0"
  assumes a: "a < x" and b: "x < b"
  assumes inj: "\<forall>y. a < y \<and> y < b \<longrightarrow> f (g y) = y"
  assumes cont: "isCont g x"
  shows "DERIV g x :> inverse D"
unfolding DERIV_iff2
proof (rule LIM_equal2)
  show "0 < min (x - a) (b - x)"
    using a b by arith 
next
  fix y
  assume "norm (y - x) < min (x - a) (b - x)"
  hence "a < y" and "y < b" 
    by (simp_all add: abs_less_iff)
  thus "(g y - g x) / (y - x) =
        inverse ((f (g y) - x) / (g y - g x))"
    by (simp add: inj)
next
  have "(\<lambda>z. (f z - f (g x)) / (z - g x)) -- g x --> D"
    by (rule der [unfolded DERIV_iff2])
  hence 1: "(\<lambda>z. (f z - x) / (z - g x)) -- g x --> D"
    using inj a b by simp
  have 2: "\<exists>d>0. \<forall>y. y \<noteq> x \<and> norm (y - x) < d \<longrightarrow> g y \<noteq> g x"
  proof (safe intro!: exI)
    show "0 < min (x - a) (b - x)"
      using a b by simp
  next
    fix y
    assume "norm (y - x) < min (x - a) (b - x)"
    hence y: "a < y" "y < b"
      by (simp_all add: abs_less_iff)
    assume "g y = g x"
    hence "f (g y) = f (g x)" by simp
    hence "y = x" using inj y a b by simp
    also assume "y \<noteq> x"
    finally show False by simp
  qed
  have "(\<lambda>y. (f (g y) - x) / (g y - g x)) -- x --> D"
    using cont 1 2 by (rule isCont_LIM_compose2)
  thus "(\<lambda>y. inverse ((f (g y) - x) / (g y - g x)))
        -- x --> inverse D"
    using neq by (rule tendsto_inverse)
qed


subsection {* Generalized Mean Value Theorem *}

theorem GMVT:
  fixes a b :: real
  assumes alb: "a < b"
    and fc: "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x"
    and fd: "\<forall>x. a < x \<and> x < b \<longrightarrow> f differentiable x"
    and gc: "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont g x"
    and gd: "\<forall>x. a < x \<and> x < b \<longrightarrow> g differentiable x"
  shows "\<exists>g'c f'c c. DERIV g c :> g'c \<and> DERIV f c :> f'c \<and> a < c \<and> c < b \<and> ((f b - f a) * g'c) = ((g b - g a) * f'c)"
proof -
  let ?h = "\<lambda>x. (f b - f a)*(g x) - (g b - g a)*(f x)"
  from assms have "a < b" by simp
  moreover have "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont ?h x"
    using fc gc by simp
  moreover have "\<forall>x. a < x \<and> x < b \<longrightarrow> ?h differentiable x"
    using fd gd by simp
  ultimately have "\<exists>l z. a < z \<and> z < b \<and> DERIV ?h z :> l \<and> ?h b - ?h a = (b - a) * l" by (rule MVT)
  then obtain l where ldef: "\<exists>z. a < z \<and> z < b \<and> DERIV ?h z :> l \<and> ?h b - ?h a = (b - a) * l" ..
  then obtain c where cdef: "a < c \<and> c < b \<and> DERIV ?h c :> l \<and> ?h b - ?h a = (b - a) * l" ..

  from cdef have cint: "a < c \<and> c < b" by auto
  with gd have "g differentiable c" by simp
  hence "\<exists>D. DERIV g c :> D" by (rule differentiableD)
  then obtain g'c where g'cdef: "DERIV g c :> g'c" ..

  from cdef have "a < c \<and> c < b" by auto
  with fd have "f differentiable c" by simp
  hence "\<exists>D. DERIV f c :> D" by (rule differentiableD)
  then obtain f'c where f'cdef: "DERIV f c :> f'c" ..

  from cdef have "DERIV ?h c :> l" by auto
  moreover have "DERIV ?h c :>  g'c * (f b - f a) - f'c * (g b - g a)"
    using g'cdef f'cdef by (auto intro!: DERIV_intros)
  ultimately have leq: "l =  g'c * (f b - f a) - f'c * (g b - g a)" by (rule DERIV_unique)

  {
    from cdef have "?h b - ?h a = (b - a) * l" by auto
    also with leq have "\<dots> = (b - a) * (g'c * (f b - f a) - f'c * (g b - g a))" by simp
    finally have "?h b - ?h a = (b - a) * (g'c * (f b - f a) - f'c * (g b - g a))" by simp
  }
  moreover
  {
    have "?h b - ?h a =
         ((f b)*(g b) - (f a)*(g b) - (g b)*(f b) + (g a)*(f b)) -
          ((f b)*(g a) - (f a)*(g a) - (g b)*(f a) + (g a)*(f a))"
      by (simp add: algebra_simps)
    hence "?h b - ?h a = 0" by auto
  }
  ultimately have "(b - a) * (g'c * (f b - f a) - f'c * (g b - g a)) = 0" by auto
  with alb have "g'c * (f b - f a) - f'c * (g b - g a) = 0" by simp
  hence "g'c * (f b - f a) = f'c * (g b - g a)" by simp
  hence "(f b - f a) * g'c = (g b - g a) * f'c" by (simp add: mult_ac)

  with g'cdef f'cdef cint show ?thesis by auto
qed


subsection {* Theorems about Limits *}

(* need to rename second isCont_inverse *)

lemma isCont_inv_fun:
  fixes f g :: "real \<Rightarrow> real"
  shows "[| 0 < d; \<forall>z. \<bar>z - x\<bar> \<le> d --> g(f(z)) = z;  
         \<forall>z. \<bar>z - x\<bar> \<le> d --> isCont f z |]  
      ==> isCont g (f x)"
by (rule isCont_inverse_function)

lemma isCont_inv_fun_inv:
  fixes f g :: "real \<Rightarrow> real"
  shows "[| 0 < d;  
         \<forall>z. \<bar>z - x\<bar> \<le> d --> g(f(z)) = z;  
         \<forall>z. \<bar>z - x\<bar> \<le> d --> isCont f z |]  
       ==> \<exists>e. 0 < e &  
             (\<forall>y. 0 < \<bar>y - f(x)\<bar> & \<bar>y - f(x)\<bar> < e --> f(g(y)) = y)"
apply (drule isCont_inj_range)
prefer 2 apply (assumption, assumption, auto)
apply (rule_tac x = e in exI, auto)
apply (rotate_tac 2)
apply (drule_tac x = y in spec, auto)
done


text{*Bartle/Sherbert: Introduction to Real Analysis, Theorem 4.2.9, p. 110*}
lemma LIM_fun_gt_zero:
     "[| f -- c --> (l::real); 0 < l |]  
         ==> \<exists>r. 0 < r & (\<forall>x::real. x \<noteq> c & \<bar>c - x\<bar> < r --> 0 < f x)"
apply (drule (1) LIM_D, clarify)
apply (rule_tac x = s in exI)
apply (simp add: abs_less_iff)
done

lemma LIM_fun_less_zero:
     "[| f -- c --> (l::real); l < 0 |]  
      ==> \<exists>r. 0 < r & (\<forall>x::real. x \<noteq> c & \<bar>c - x\<bar> < r --> f x < 0)"
apply (drule LIM_D [where r="-l"], simp, clarify)
apply (rule_tac x = s in exI)
apply (simp add: abs_less_iff)
done

lemma LIM_fun_not_zero:
     "[| f -- c --> (l::real); l \<noteq> 0 |] 
      ==> \<exists>r. 0 < r & (\<forall>x::real. x \<noteq> c & \<bar>c - x\<bar> < r --> f x \<noteq> 0)"
apply (rule linorder_cases [of l 0])
apply (drule (1) LIM_fun_less_zero, force)
apply simp
apply (drule (1) LIM_fun_gt_zero, force)
done

end
