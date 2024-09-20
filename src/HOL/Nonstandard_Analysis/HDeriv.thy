(*  Title:      HOL/Nonstandard_Analysis/HDeriv.thy
    Author:     Jacques D. Fleuriot
    Copyright:  1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

section \<open>Differentiation (Nonstandard)\<close>

theory HDeriv
  imports HLim
begin

text \<open>Nonstandard Definitions.\<close>

definition nsderiv :: "['a::real_normed_field \<Rightarrow> 'a, 'a, 'a] \<Rightarrow> bool"
    (\<open>(NSDERIV (_)/ (_)/ :> (_))\<close> [1000, 1000, 60] 60)
  where "NSDERIV f x :> D \<longleftrightarrow>
    (\<forall>h \<in> Infinitesimal - {0}. (( *f* f)(star_of x + h) - star_of (f x)) / h \<approx> star_of D)"

definition NSdifferentiable :: "['a::real_normed_field \<Rightarrow> 'a, 'a] \<Rightarrow> bool"
    (infixl \<open>NSdifferentiable\<close> 60)
  where "f NSdifferentiable x \<longleftrightarrow> (\<exists>D. NSDERIV f x :> D)"

definition increment :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> hypreal \<Rightarrow> hypreal"
  where "increment f x h =
    (SOME inc. f NSdifferentiable x \<and> inc = ( *f* f) (hypreal_of_real x + h) - hypreal_of_real (f x))"


subsection \<open>Derivatives\<close>

lemma DERIV_NS_iff: "(DERIV f x :> D) \<longleftrightarrow> (\<lambda>h. (f (x + h) - f x) / h) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S D"
  by (simp add: DERIV_def LIM_NSLIM_iff)

lemma NS_DERIV_D: "DERIV f x :> D \<Longrightarrow> (\<lambda>h. (f (x + h) - f x) / h) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S D"
  by (simp add: DERIV_def LIM_NSLIM_iff)

lemma Infinitesimal_of_hypreal:
  "x \<in> Infinitesimal \<Longrightarrow> (( *f* of_real) x::'a::real_normed_div_algebra star) \<in> Infinitesimal"
  by (metis Infinitesimal_of_hypreal_iff of_hypreal_def)

lemma of_hypreal_eq_0_iff: "\<And>x. (( *f* of_real) x = (0::'a::real_algebra_1 star)) = (x = 0)"
  by transfer (rule of_real_eq_0_iff)

lemma NSDeriv_unique:
  assumes "NSDERIV f x :> D" "NSDERIV f x :> E"
  shows "NSDERIV f x :> D \<Longrightarrow> NSDERIV f x :> E \<Longrightarrow> D = E"
proof -
  have "\<exists>s. (s::'a star) \<in> Infinitesimal - {0}"
    by (metis Diff_iff HDeriv.of_hypreal_eq_0_iff Infinitesimal_epsilon Infinitesimal_of_hypreal epsilon_not_zero singletonD)
  with assms show ?thesis
    by (meson approx_trans3 nsderiv_def star_of_approx_iff)
qed

text \<open>First \<open>NSDERIV\<close> in terms of \<open>NSLIM\<close>.\<close>

text \<open>First equivalence.\<close>
lemma NSDERIV_NSLIM_iff: "(NSDERIV f x :> D) \<longleftrightarrow> (\<lambda>h. (f (x + h) - f x) / h) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S D"
  by (auto simp add: nsderiv_def NSLIM_def starfun_lambda_cancel mem_infmal_iff)

text \<open>Second equivalence.\<close>
lemma NSDERIV_NSLIM_iff2: "(NSDERIV f x :> D) \<longleftrightarrow> (\<lambda>z. (f z - f x) / (z - x)) \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S D"
  by (simp add: NSDERIV_NSLIM_iff DERIV_LIM_iff LIM_NSLIM_iff [symmetric])

text \<open>While we're at it!\<close>
lemma NSDERIV_iff2:
  "(NSDERIV f x :> D) \<longleftrightarrow>
    (\<forall>w. w \<noteq> star_of x \<and> w \<approx> star_of x \<longrightarrow> ( *f* (\<lambda>z. (f z - f x) / (z - x))) w \<approx> star_of D)"
  by (simp add: NSDERIV_NSLIM_iff2 NSLIM_def)

lemma NSDERIVD5:
  "\<lbrakk>NSDERIV f x :> D; u \<approx> hypreal_of_real x\<rbrakk> \<Longrightarrow>
     ( *f* (\<lambda>z. f z - f x)) u \<approx> hypreal_of_real D * (u - hypreal_of_real x)"
  unfolding NSDERIV_iff2
  apply (case_tac "u = hypreal_of_real x", auto)
  by (metis (mono_tags, lifting) HFinite_star_of Infinitesimal_ratio approx_def approx_minus_iff approx_mult_subst approx_star_of_HFinite approx_sym mult_zero_right right_minus_eq)

lemma NSDERIVD4:
  "\<lbrakk>NSDERIV f x :> D; h \<in> Infinitesimal\<rbrakk>
    \<Longrightarrow> ( *f* f)(hypreal_of_real x + h) - hypreal_of_real (f x) \<approx> hypreal_of_real D * h"
  apply (clarsimp simp add: nsderiv_def)
  apply (case_tac "h = 0", simp)
  by (meson DiffI Infinitesimal_approx Infinitesimal_ratio Infinitesimal_star_of_mult2 approx_star_of_HFinite singletonD)

text \<open>Differentiability implies continuity nice and simple "algebraic" proof.\<close>
lemma NSDERIV_isNSCont: 
  assumes "NSDERIV f x :> D" shows "isNSCont f x"
  unfolding isNSCont_NSLIM_iff NSLIM_def
proof clarify
  fix x'
  assume "x' \<noteq> star_of x" "x' \<approx> star_of x"
  then have m0: "x' - star_of x \<in> Infinitesimal - {0}"
    using bex_Infinitesimal_iff by auto
  then have "(( *f* f) x' - star_of (f x)) / (x' - star_of x) \<approx> star_of D"
    by (metis \<open>x' \<approx> star_of x\<close> add_diff_cancel_left' assms bex_Infinitesimal_iff2 nsderiv_def)
  then have "(( *f* f) x' - star_of (f x)) / (x' - star_of x) \<in> HFinite"
    by (metis approx_star_of_HFinite)  
  then show "( *f* f) x' \<approx> star_of (f x)"
    by (metis (no_types) Diff_iff Infinitesimal_ratio m0 bex_Infinitesimal_iff insert_iff)
qed

text \<open>Differentiation rules for combinations of functions
  follow from clear, straightforward, algebraic manipulations.\<close>

text \<open>Constant function.\<close>

(* use simple constant nslimit theorem *)
lemma NSDERIV_const [simp]: "NSDERIV (\<lambda>x. k) x :> 0"
  by (simp add: NSDERIV_NSLIM_iff)

text \<open>Sum of functions- proved easily.\<close>

lemma NSDERIV_add:
  assumes "NSDERIV f x :> Da" "NSDERIV g x :> Db"
  shows "NSDERIV (\<lambda>x. f x + g x) x :> Da + Db"
proof -
  have "((\<lambda>x. f x + g x) has_field_derivative Da + Db) (at x)"
    using assms DERIV_NS_iff NSDERIV_NSLIM_iff field_differentiable_add by blast
  then show ?thesis
    by (simp add: DERIV_NS_iff NSDERIV_NSLIM_iff)
qed

text \<open>Product of functions - Proof is simple.\<close>

lemma NSDERIV_mult:
  assumes "NSDERIV g x :> Db" "NSDERIV f x :> Da"
  shows "NSDERIV (\<lambda>x. f x * g x) x :> (Da * g x) + (Db * f x)"
proof -
  have "(f has_field_derivative Da) (at x)" "(g has_field_derivative Db) (at x)"
    using assms by (simp_all add: DERIV_NS_iff NSDERIV_NSLIM_iff)
  then have "((\<lambda>a. f a * g a) has_field_derivative Da * g x + Db * f x) (at x)"
    using DERIV_mult by blast
  then show ?thesis
    by (simp add: DERIV_NS_iff NSDERIV_NSLIM_iff)
qed

text \<open>Multiplying by a constant.\<close>
lemma NSDERIV_cmult: "NSDERIV f x :> D \<Longrightarrow> NSDERIV (\<lambda>x. c * f x) x :> c * D"
  unfolding times_divide_eq_right [symmetric] NSDERIV_NSLIM_iff
      minus_mult_right right_diff_distrib [symmetric]
  by (erule NSLIM_const [THEN NSLIM_mult])

text \<open>Negation of function.\<close>
lemma NSDERIV_minus: "NSDERIV f x :> D \<Longrightarrow> NSDERIV (\<lambda>x. - f x) x :> - D"
proof (simp add: NSDERIV_NSLIM_iff)
  assume "(\<lambda>h. (f (x + h) - f x) / h) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S D"
  then have deriv: "(\<lambda>h. - ((f(x+h) - f x) / h)) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S - D"
    by (rule NSLIM_minus)
  have "\<forall>h. - ((f (x + h) - f x) / h) = (- f (x + h) + f x) / h"
    by (simp add: minus_divide_left)
  with deriv have "(\<lambda>h. (- f (x + h) + f x) / h) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S - D"
    by simp
  then show "(\<lambda>h. (f (x + h) - f x) / h) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S D \<Longrightarrow> (\<lambda>h. (f x - f (x + h)) / h) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S - D"
    by simp
qed

text \<open>Subtraction.\<close>
lemma NSDERIV_add_minus:
  "NSDERIV f x :> Da \<Longrightarrow> NSDERIV g x :> Db \<Longrightarrow> NSDERIV (\<lambda>x. f x + - g x) x :> Da + - Db"
  by (blast dest: NSDERIV_add NSDERIV_minus)

lemma NSDERIV_diff:
  "NSDERIV f x :> Da \<Longrightarrow> NSDERIV g x :> Db \<Longrightarrow> NSDERIV (\<lambda>x. f x - g x) x :> Da - Db"
  using NSDERIV_add_minus [of f x Da g Db] by simp

text \<open>Similarly to the above, the chain rule admits an entirely
  straightforward derivation. Compare this with Harrison's
  HOL proof of the chain rule, which proved to be trickier and
  required an alternative characterisation of differentiability-
  the so-called Carathedory derivative. Our main problem is
  manipulation of terms.\<close>


subsection \<open>Lemmas\<close>

lemma NSDERIV_zero:
  "\<lbrakk>NSDERIV g x :> D; ( *f* g) (star_of x + y) = star_of (g x); y \<in> Infinitesimal; y \<noteq> 0\<rbrakk>
    \<Longrightarrow> D = 0"
  by (force simp add: nsderiv_def)

text \<open>Can be proved differently using \<open>NSLIM_isCont_iff\<close>.\<close>
lemma NSDERIV_approx:
  "NSDERIV f x :> D \<Longrightarrow> h \<in> Infinitesimal \<Longrightarrow> h \<noteq> 0 \<Longrightarrow>
    ( *f* f) (star_of x + h) - star_of (f x) \<approx> 0"
  by (meson DiffI Infinitesimal_ratio approx_star_of_HFinite mem_infmal_iff nsderiv_def singletonD)

text \<open>From one version of differentiability

        \<open>f x - f a\<close>
      \<open>-------------- \<approx> Db\<close>
          \<open>x - a\<close>
\<close>

lemma NSDERIVD1: 
    "\<lbrakk>NSDERIV f (g x) :> Da;
     ( *f* g) (star_of x + y) \<noteq> star_of (g x);
     ( *f* g) (star_of x + y) \<approx> star_of (g x)\<rbrakk>
    \<Longrightarrow> (( *f* f) (( *f* g) (star_of x + y)) -
         star_of (f (g x))) / (( *f* g) (star_of x + y) - star_of (g x)) \<approx>
        star_of Da"
  by (auto simp add: NSDERIV_NSLIM_iff2 NSLIM_def)

text \<open>From other version of differentiability

      \<open>f (x + h) - f x\<close>
     \<open>------------------ \<approx> Db\<close>
             \<open>h\<close>
\<close>

lemma NSDERIVD2: "[| NSDERIV g x :> Db; y \<in> Infinitesimal; y \<noteq> 0 |]
      ==> (( *f* g) (star_of(x) + y) - star_of(g x)) / y
          \<approx> star_of(Db)"
  by (auto simp add: NSDERIV_NSLIM_iff NSLIM_def mem_infmal_iff starfun_lambda_cancel)

text \<open>This proof uses both definitions of differentiability.\<close>
lemma NSDERIV_chain:
  "NSDERIV f (g x) :> Da \<Longrightarrow> NSDERIV g x :> Db \<Longrightarrow> NSDERIV (f \<circ> g) x :> Da * Db"
  using DERIV_NS_iff DERIV_chain NSDERIV_NSLIM_iff by blast

text \<open>Differentiation of natural number powers.\<close>
lemma NSDERIV_Id [simp]: "NSDERIV (\<lambda>x. x) x :> 1"
  by (simp add: NSDERIV_NSLIM_iff NSLIM_def del: divide_self_if)

lemma NSDERIV_cmult_Id [simp]: "NSDERIV ((*) c) x :> c"
  using NSDERIV_Id [THEN NSDERIV_cmult] by simp

lemma NSDERIV_inverse:
  fixes x :: "'a::real_normed_field"
  assumes "x \<noteq> 0" \<comment> \<open>can't get rid of \<^term>\<open>x \<noteq> 0\<close> because it isn't continuous at zero\<close>
  shows "NSDERIV (\<lambda>x. inverse x) x :> - (inverse x ^ Suc (Suc 0))"
proof -
  {
    fix h :: "'a star"
    assume h_Inf: "h \<in> Infinitesimal"
    from this assms have not_0: "star_of x + h \<noteq> 0"
      by (rule Infinitesimal_add_not_zero)
    assume "h \<noteq> 0"
    from h_Inf have "h * star_of x \<in> Infinitesimal"
      by (rule Infinitesimal_HFinite_mult) simp
    with assms have "inverse (- (h * star_of x) + - (star_of x * star_of x)) \<approx>
      inverse (- (star_of x * star_of x))"
    proof -
      have "- (h * star_of x) + - (star_of x * star_of x) \<approx> - (star_of x * star_of x)"
        using \<open>h * star_of x \<in> Infinitesimal\<close> assms bex_Infinitesimal_iff by fastforce
      then show ?thesis
        by (metis assms mult_eq_0_iff neg_equal_0_iff_equal star_of_approx_inverse star_of_minus star_of_mult)
    qed
    moreover from not_0 \<open>h \<noteq> 0\<close> assms
    have "inverse (- (h * star_of x) + - (star_of x * star_of x)) 
          = (inverse (star_of x + h) - inverse (star_of x)) / h"
      by (simp add: division_ring_inverse_diff inverse_mult_distrib [symmetric]
          inverse_minus_eq [symmetric] algebra_simps)
    ultimately have "(inverse (star_of x + h) - inverse (star_of x)) / h \<approx>
      - (inverse (star_of x) * inverse (star_of x))"
      using assms by simp
  }
  then show ?thesis by (simp add: nsderiv_def)
qed


subsubsection \<open>Equivalence of NS and Standard definitions\<close>

lemma divideR_eq_divide: "x /\<^sub>R y = x / y"
  by (simp add: divide_inverse mult.commute)

text \<open>Now equivalence between \<open>NSDERIV\<close> and \<open>DERIV\<close>.\<close>
lemma NSDERIV_DERIV_iff: "NSDERIV f x :> D \<longleftrightarrow> DERIV f x :> D"
  by (simp add: DERIV_def NSDERIV_NSLIM_iff LIM_NSLIM_iff)

text \<open>NS version.\<close>
lemma NSDERIV_pow: "NSDERIV (\<lambda>x. x ^ n) x :> real n * (x ^ (n - Suc 0))"
  by (simp add: NSDERIV_DERIV_iff DERIV_pow)

text \<open>Derivative of inverse.\<close>
lemma NSDERIV_inverse_fun:
  "NSDERIV f x :> d \<Longrightarrow> f x \<noteq> 0 \<Longrightarrow>
    NSDERIV (\<lambda>x. inverse (f x)) x :> (- (d * inverse (f x ^ Suc (Suc 0))))"
  for x :: "'a::{real_normed_field}"
  by (simp add: NSDERIV_DERIV_iff DERIV_inverse_fun del: power_Suc)

text \<open>Derivative of quotient.\<close>
lemma NSDERIV_quotient:
  fixes x :: "'a::real_normed_field"
  shows "NSDERIV f x :> d \<Longrightarrow> NSDERIV g x :> e \<Longrightarrow> g x \<noteq> 0 \<Longrightarrow>
    NSDERIV (\<lambda>y. f y / g y) x :> (d * g x - (e * f x)) / (g x ^ Suc (Suc 0))"
  by (simp add: NSDERIV_DERIV_iff DERIV_quotient del: power_Suc)

lemma CARAT_NSDERIV:
  "NSDERIV f x :> l \<Longrightarrow> \<exists>g. (\<forall>z. f z - f x = g z * (z - x)) \<and> isNSCont g x \<and> g x = l"
  by (simp add: CARAT_DERIV NSDERIV_DERIV_iff isNSCont_isCont_iff)

lemma hypreal_eq_minus_iff3: "x = y + z \<longleftrightarrow> x + - z = y"
  for x y z :: hypreal
  by auto

lemma CARAT_DERIVD:
  assumes all: "\<forall>z. f z - f x = g z * (z - x)"
    and nsc: "isNSCont g x"
  shows "NSDERIV f x :> g x"
proof -
  from nsc have "\<forall>w. w \<noteq> star_of x \<and> w \<approx> star_of x \<longrightarrow>
       ( *f* g) w * (w - star_of x) / (w - star_of x) \<approx> star_of (g x)"
    by (simp add: isNSCont_def)
  with all show ?thesis
    by (simp add: NSDERIV_iff2 starfun_if_eq cong: if_cong)
qed


subsubsection \<open>Differentiability predicate\<close>

lemma NSdifferentiableD: "f NSdifferentiable x \<Longrightarrow> \<exists>D. NSDERIV f x :> D"
  by (simp add: NSdifferentiable_def)

lemma NSdifferentiableI: "NSDERIV f x :> D \<Longrightarrow> f NSdifferentiable x"
  by (force simp add: NSdifferentiable_def)


subsection \<open>(NS) Increment\<close>

lemma incrementI:
  "f NSdifferentiable x \<Longrightarrow>
    increment f x h = ( *f* f) (hypreal_of_real x + h) - hypreal_of_real (f x)"
  by (simp add: increment_def)

lemma incrementI2:
  "NSDERIV f x :> D \<Longrightarrow>
    increment f x h = ( *f* f) (hypreal_of_real x + h) - hypreal_of_real (f x)"
  by (erule NSdifferentiableI [THEN incrementI])

text \<open>The Increment theorem -- Keisler p. 65.\<close>
lemma increment_thm:
  assumes "NSDERIV f x :> D" "h \<in> Infinitesimal" "h \<noteq> 0"
  shows "\<exists>e \<in> Infinitesimal. increment f x h = hypreal_of_real D * h + e * h"
proof -
  have inc: "increment f x h = ( *f* f) (hypreal_of_real x + h) - hypreal_of_real (f x)"
    using assms(1) incrementI2 by auto
  have "(( *f* f) (hypreal_of_real x + h) - hypreal_of_real (f x)) / h \<approx> hypreal_of_real D"
    by (simp add: NSDERIVD2 assms)
  then obtain y where "y \<in> Infinitesimal" 
    "(( *f* f) (hypreal_of_real x + h) - hypreal_of_real (f x)) / h = hypreal_of_real D + y"
    by (metis bex_Infinitesimal_iff2)
  then have "increment f x h / h = hypreal_of_real D + y"
    by (metis inc) 
  then show ?thesis
    by (metis (no_types) \<open>y \<in> Infinitesimal\<close> \<open>h \<noteq> 0\<close> distrib_right mult.commute nonzero_mult_div_cancel_left times_divide_eq_right)
qed

lemma increment_approx_zero: "NSDERIV f x :> D \<Longrightarrow> h \<approx> 0 \<Longrightarrow> h \<noteq> 0 \<Longrightarrow> increment f x h \<approx> 0"
  by (simp add: NSDERIV_approx incrementI2 mem_infmal_iff)

end
