(*  Author: John Harrison, Marco Maggesi, Graziano Gentili, Gianni Ciolli, Valentina Bruno
    Ported from "hol_light/Multivariate/canal.ml" by L C Paulson (2014)
*)

header {* Complex Analysis Basics *}

theory Complex_Analysis_Basics
imports  "~~/src/HOL/Multivariate_Analysis/Cartesian_Euclidean_Space"
begin

subsection{*General lemmas*}

lemma has_derivative_mult_right:
  fixes c:: "'a :: real_normed_algebra"
  shows "((op * c) has_derivative (op * c)) F"
by (rule has_derivative_mult_right [OF has_derivative_id])

lemma has_derivative_of_real[derivative_intros, simp]: 
  "(f has_derivative f') F \<Longrightarrow> ((\<lambda>x. of_real (f x)) has_derivative (\<lambda>x. of_real (f' x))) F"
  using bounded_linear.has_derivative[OF bounded_linear_of_real] .

lemma has_vector_derivative_real_complex:
  "DERIV f (of_real a) :> f' \<Longrightarrow> ((\<lambda>x. f (of_real x)) has_vector_derivative f') (at a)"
  using has_derivative_compose[of of_real of_real a UNIV f "op * f'"]
  by (simp add: scaleR_conv_of_real ac_simps has_vector_derivative_def has_field_derivative_def)

lemma fact_cancel:
  fixes c :: "'a::real_field"
  shows "of_nat (Suc n) * c / of_nat (fact (Suc n)) = c / of_nat (fact n)"
  by (simp add: of_nat_mult del: of_nat_Suc times_nat.simps)
lemma linear_times:
  fixes c::"'a::real_algebra" shows "linear (\<lambda>x. c * x)"
  by (auto simp: linearI distrib_left)

lemma bilinear_times:
  fixes c::"'a::real_algebra" shows "bilinear (\<lambda>x y::'a. x*y)"
  by (auto simp: bilinear_def distrib_left distrib_right intro!: linearI)

lemma linear_cnj: "linear cnj"
  using bounded_linear.linear[OF bounded_linear_cnj] .

lemma tendsto_mult_left:
  fixes c::"'a::real_normed_algebra" 
  shows "(f ---> l) F \<Longrightarrow> ((\<lambda>x. c * (f x)) ---> c * l) F"
by (rule tendsto_mult [OF tendsto_const])

lemma tendsto_mult_right:
  fixes c::"'a::real_normed_algebra" 
  shows "(f ---> l) F \<Longrightarrow> ((\<lambda>x. (f x) * c) ---> l * c) F"
by (rule tendsto_mult [OF _ tendsto_const])

lemma tendsto_Re_upper:
  assumes "~ (trivial_limit F)" 
          "(f ---> l) F" 
          "eventually (\<lambda>x. Re(f x) \<le> b) F"
    shows  "Re(l) \<le> b"
  by (metis assms tendsto_le [OF _ tendsto_const]  tendsto_Re)

lemma tendsto_Re_lower:
  assumes "~ (trivial_limit F)" 
          "(f ---> l) F" 
          "eventually (\<lambda>x. b \<le> Re(f x)) F"
    shows  "b \<le> Re(l)"
  by (metis assms tendsto_le [OF _ _ tendsto_const]  tendsto_Re)

lemma tendsto_Im_upper:
  assumes "~ (trivial_limit F)" 
          "(f ---> l) F" 
          "eventually (\<lambda>x. Im(f x) \<le> b) F"
    shows  "Im(l) \<le> b"
  by (metis assms tendsto_le [OF _ tendsto_const]  tendsto_Im)

lemma tendsto_Im_lower:
  assumes "~ (trivial_limit F)" 
          "(f ---> l) F" 
          "eventually (\<lambda>x. b \<le> Im(f x)) F"
    shows  "b \<le> Im(l)"
  by (metis assms tendsto_le [OF _ _ tendsto_const]  tendsto_Im)

lemma lambda_zero: "(\<lambda>h::'a::mult_zero. 0) = op * 0"
  by auto

lemma lambda_one: "(\<lambda>x::'a::monoid_mult. x) = op * 1"
  by auto

lemma has_real_derivative:
  fixes f :: "real \<Rightarrow> real" 
  assumes "(f has_derivative f') F"
  obtains c where "(f has_real_derivative c) F"
proof -
  obtain c where "f' = (\<lambda>x. x * c)"
    by (metis assms has_derivative_bounded_linear real_bounded_linear)
  then show ?thesis
    by (metis assms that has_field_derivative_def mult_commute_abs)
qed

lemma has_real_derivative_iff:
  fixes f :: "real \<Rightarrow> real" 
  shows "(\<exists>c. (f has_real_derivative c) F) = (\<exists>D. (f has_derivative D) F)"
  by (metis has_field_derivative_def has_real_derivative)

lemma continuous_mult_left:
  fixes c::"'a::real_normed_algebra" 
  shows "continuous F f \<Longrightarrow> continuous F (\<lambda>x. c * f x)"
by (rule continuous_mult [OF continuous_const])

lemma continuous_mult_right:
  fixes c::"'a::real_normed_algebra" 
  shows "continuous F f \<Longrightarrow> continuous F (\<lambda>x. f x * c)"
by (rule continuous_mult [OF _ continuous_const])

lemma continuous_on_mult_left:
  fixes c::"'a::real_normed_algebra" 
  shows "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. c * f x)"
by (rule continuous_on_mult [OF continuous_on_const])

lemma continuous_on_mult_right:
  fixes c::"'a::real_normed_algebra" 
  shows "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. f x * c)"
by (rule continuous_on_mult [OF _ continuous_on_const])

lemma uniformly_continuous_on_cmul_right [continuous_intros]:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  shows "uniformly_continuous_on s f \<Longrightarrow> uniformly_continuous_on s (\<lambda>x. f x * c)"
  using bounded_linear.uniformly_continuous_on[OF bounded_linear_mult_left] . 

lemma uniformly_continuous_on_cmul_left[continuous_intros]:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  assumes "uniformly_continuous_on s f"
    shows "uniformly_continuous_on s (\<lambda>x. c * f x)"
by (metis assms bounded_linear.uniformly_continuous_on bounded_linear_mult_right)

lemma continuous_within_norm_id [continuous_intros]: "continuous (at x within S) norm"
  by (rule continuous_norm [OF continuous_ident])

lemma continuous_on_norm_id [continuous_intros]: "continuous_on S norm"
  by (intro continuous_on_id continuous_on_norm)

subsection{*DERIV stuff*}

lemma DERIV_zero_connected_constant:
  fixes f :: "'a::{real_normed_field,euclidean_space} \<Rightarrow> 'a"
  assumes "connected s"
      and "open s"
      and "finite k"
      and "continuous_on s f"
      and "\<forall>x\<in>(s - k). DERIV f x :> 0"
    obtains c where "\<And>x. x \<in> s \<Longrightarrow> f(x) = c"
using has_derivative_zero_connected_constant [OF assms(1-4)] assms
by (metis DERIV_const has_derivative_const Diff_iff at_within_open frechet_derivative_at has_field_derivative_def)

lemma DERIV_zero_constant:
  fixes f :: "'a::{real_normed_field, real_inner} \<Rightarrow> 'a"
  shows    "\<lbrakk>convex s;
             \<And>x. x\<in>s \<Longrightarrow> (f has_field_derivative 0) (at x within s)\<rbrakk> 
             \<Longrightarrow> \<exists>c. \<forall>x \<in> s. f(x) = c"
  by (auto simp: has_field_derivative_def lambda_zero intro: has_derivative_zero_constant)

lemma DERIV_zero_unique:
  fixes f :: "'a::{real_normed_field, real_inner} \<Rightarrow> 'a"
  assumes "convex s"
      and d0: "\<And>x. x\<in>s \<Longrightarrow> (f has_field_derivative 0) (at x within s)"
      and "a \<in> s"
      and "x \<in> s"
    shows "f x = f a"
  by (rule has_derivative_zero_unique [OF assms(1) _ assms(4,3)])
     (metis d0 has_field_derivative_imp_has_derivative lambda_zero)

lemma DERIV_zero_connected_unique:
  fixes f :: "'a::{real_normed_field, real_inner} \<Rightarrow> 'a"
  assumes "connected s"
      and "open s"
      and d0: "\<And>x. x\<in>s \<Longrightarrow> DERIV f x :> 0"
      and "a \<in> s"
      and "x \<in> s"
    shows "f x = f a" 
    by (rule has_derivative_zero_unique_connected [OF assms(2,1) _ assms(5,4)])
       (metis has_field_derivative_def lambda_zero d0)

lemma DERIV_transform_within:
  assumes "(f has_field_derivative f') (at a within s)"
      and "0 < d" "a \<in> s"
      and "\<And>x. x\<in>s \<Longrightarrow> dist x a < d \<Longrightarrow> f x = g x"
    shows "(g has_field_derivative f') (at a within s)"
  using assms unfolding has_field_derivative_def
  by (blast intro: has_derivative_transform_within)

lemma DERIV_transform_within_open:
  assumes "DERIV f a :> f'"
      and "open s" "a \<in> s"
      and "\<And>x. x\<in>s \<Longrightarrow> f x = g x"
    shows "DERIV g a :> f'"
  using assms unfolding has_field_derivative_def
by (metis has_derivative_transform_within_open)

lemma DERIV_transform_at:
  assumes "DERIV f a :> f'"
      and "0 < d"
      and "\<And>x. dist x a < d \<Longrightarrow> f x = g x"
    shows "DERIV g a :> f'"
  by (blast intro: assms DERIV_transform_within)

subsection {*Some limit theorems about real part of real series etc.*}

(*MOVE? But not to Finite_Cartesian_Product*)
lemma sums_vec_nth :
  assumes "f sums a"
  shows "(\<lambda>x. f x $ i) sums a $ i"
using assms unfolding sums_def
by (auto dest: tendsto_vec_nth [where i=i])

lemma summable_vec_nth :
  assumes "summable f"
  shows "summable (\<lambda>x. f x $ i)"
using assms unfolding summable_def
by (blast intro: sums_vec_nth)

subsection {*Complex number lemmas *}

lemma
  shows open_halfspace_Re_lt: "open {z. Re(z) < b}"
    and open_halfspace_Re_gt: "open {z. Re(z) > b}"
    and closed_halfspace_Re_ge: "closed {z. Re(z) \<ge> b}"
    and closed_halfspace_Re_le: "closed {z. Re(z) \<le> b}"
    and closed_halfspace_Re_eq: "closed {z. Re(z) = b}"
    and open_halfspace_Im_lt: "open {z. Im(z) < b}"
    and open_halfspace_Im_gt: "open {z. Im(z) > b}"
    and closed_halfspace_Im_ge: "closed {z. Im(z) \<ge> b}"
    and closed_halfspace_Im_le: "closed {z. Im(z) \<le> b}"
    and closed_halfspace_Im_eq: "closed {z. Im(z) = b}"
  by (intro open_Collect_less closed_Collect_le closed_Collect_eq isCont_Re
            isCont_Im isCont_ident isCont_const)+

lemma closed_complex_Reals: "closed (Reals :: complex set)"
proof -
  have "(Reals :: complex set) = {z. Im z = 0}"
    by (auto simp: complex_is_Real_iff)
  then show ?thesis
    by (metis closed_halfspace_Im_eq)
qed

lemma real_lim:
  fixes l::complex
  assumes "(f ---> l) F" and "~(trivial_limit F)" and "eventually P F" and "\<And>a. P a \<Longrightarrow> f a \<in> \<real>"
  shows  "l \<in> \<real>"
proof (rule Lim_in_closed_set[OF closed_complex_Reals _ assms(2,1)])
  show "eventually (\<lambda>x. f x \<in> \<real>) F"
    using assms(3, 4) by (auto intro: eventually_mono)
qed

lemma real_lim_sequentially:
  fixes l::complex
  shows "(f ---> l) sequentially \<Longrightarrow> (\<exists>N. \<forall>n\<ge>N. f n \<in> \<real>) \<Longrightarrow> l \<in> \<real>"
by (rule real_lim [where F=sequentially]) (auto simp: eventually_sequentially)

lemma real_series: 
  fixes l::complex
  shows "f sums l \<Longrightarrow> (\<And>n. f n \<in> \<real>) \<Longrightarrow> l \<in> \<real>"
unfolding sums_def
by (metis real_lim_sequentially setsum_in_Reals)

lemma Lim_null_comparison_Re:
   "eventually (\<lambda>x. norm(f x) \<le> Re(g x)) F \<Longrightarrow>  (g ---> 0) F \<Longrightarrow> (f ---> 0) F"
  by (metis Lim_null_comparison complex_Re_zero tendsto_Re)

subsection{*Holomorphic functions*}

definition complex_differentiable :: "[complex \<Rightarrow> complex, complex filter] \<Rightarrow> bool"
           (infixr "(complex'_differentiable)" 50)  
  where "f complex_differentiable F \<equiv> \<exists>f'. (f has_field_derivative f') F"

lemma complex_differentiable_imp_continuous_at:
    "f complex_differentiable (at x within s) \<Longrightarrow> continuous (at x within s) f"
  by (metis DERIV_continuous complex_differentiable_def)

lemma complex_differentiable_within_subset:
    "\<lbrakk>f complex_differentiable (at x within s); t \<subseteq> s\<rbrakk>
     \<Longrightarrow> f complex_differentiable (at x within t)"
  by (metis DERIV_subset complex_differentiable_def)

lemma complex_differentiable_at_within:
    "\<lbrakk>f complex_differentiable (at x)\<rbrakk>
     \<Longrightarrow> f complex_differentiable (at x within s)"
  unfolding complex_differentiable_def
  by (metis DERIV_subset top_greatest)

lemma complex_differentiable_linear: "(op * c) complex_differentiable F"
proof -
  show ?thesis
    unfolding complex_differentiable_def has_field_derivative_def mult_commute_abs
    by (force intro: has_derivative_mult_right)
qed

lemma complex_differentiable_const: "(\<lambda>z. c) complex_differentiable F"
  unfolding complex_differentiable_def has_field_derivative_def
  by (rule exI [where x=0])
     (metis has_derivative_const lambda_zero) 

lemma complex_differentiable_ident: "(\<lambda>z. z) complex_differentiable F"
  unfolding complex_differentiable_def has_field_derivative_def
  by (rule exI [where x=1])
     (simp add: lambda_one [symmetric])

lemma complex_differentiable_id: "id complex_differentiable F"
  unfolding id_def by (rule complex_differentiable_ident)

lemma complex_differentiable_minus:
  "f complex_differentiable F \<Longrightarrow> (\<lambda>z. - (f z)) complex_differentiable F"
  using assms unfolding complex_differentiable_def
  by (metis field_differentiable_minus)

lemma complex_differentiable_add:
  assumes "f complex_differentiable F" "g complex_differentiable F"
    shows "(\<lambda>z. f z + g z) complex_differentiable F"
  using assms unfolding complex_differentiable_def
  by (metis field_differentiable_add)

lemma complex_differentiable_setsum:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i) complex_differentiable F) \<Longrightarrow> (\<lambda>z. \<Sum>i\<in>I. f i z) complex_differentiable F"
  by (induct I rule: infinite_finite_induct)
     (auto intro: complex_differentiable_add complex_differentiable_const)

lemma complex_differentiable_diff:
  assumes "f complex_differentiable F" "g complex_differentiable F"
    shows "(\<lambda>z. f z - g z) complex_differentiable F"
  using assms unfolding complex_differentiable_def
  by (metis field_differentiable_diff)

lemma complex_differentiable_inverse:
  assumes "f complex_differentiable (at a within s)" "f a \<noteq> 0"
  shows "(\<lambda>z. inverse (f z)) complex_differentiable (at a within s)"
  using assms unfolding complex_differentiable_def
  by (metis DERIV_inverse_fun)

lemma complex_differentiable_mult:
  assumes "f complex_differentiable (at a within s)" 
          "g complex_differentiable (at a within s)"
    shows "(\<lambda>z. f z * g z) complex_differentiable (at a within s)"
  using assms unfolding complex_differentiable_def
  by (metis DERIV_mult [of f _ a s g])
  
lemma complex_differentiable_divide:
  assumes "f complex_differentiable (at a within s)" 
          "g complex_differentiable (at a within s)"
          "g a \<noteq> 0"
    shows "(\<lambda>z. f z / g z) complex_differentiable (at a within s)"
  using assms unfolding complex_differentiable_def
  by (metis DERIV_divide [of f _ a s g])

lemma complex_differentiable_power:
  assumes "f complex_differentiable (at a within s)" 
    shows "(\<lambda>z. f z ^ n) complex_differentiable (at a within s)"
  using assms unfolding complex_differentiable_def
  by (metis DERIV_power)

lemma complex_differentiable_transform_within:
  "0 < d \<Longrightarrow>
        x \<in> s \<Longrightarrow>
        (\<And>x'. x' \<in> s \<Longrightarrow> dist x' x < d \<Longrightarrow> f x' = g x') \<Longrightarrow>
        f complex_differentiable (at x within s)
        \<Longrightarrow> g complex_differentiable (at x within s)"
  unfolding complex_differentiable_def has_field_derivative_def
  by (blast intro: has_derivative_transform_within)

lemma complex_differentiable_compose_within:
  assumes "f complex_differentiable (at a within s)" 
          "g complex_differentiable (at (f a) within f`s)"
    shows "(g o f) complex_differentiable (at a within s)"
  using assms unfolding complex_differentiable_def
  by (metis DERIV_image_chain)

lemma complex_differentiable_compose:
  "f complex_differentiable at z \<Longrightarrow> g complex_differentiable at (f z)
          \<Longrightarrow> (g o f) complex_differentiable at z"
by (metis complex_differentiable_at_within complex_differentiable_compose_within)

lemma complex_differentiable_within_open:
     "\<lbrakk>a \<in> s; open s\<rbrakk> \<Longrightarrow> f complex_differentiable at a within s \<longleftrightarrow> 
                          f complex_differentiable at a"
  unfolding complex_differentiable_def
  by (metis at_within_open)

subsection{*Caratheodory characterization.*}

lemma complex_differentiable_caratheodory_at:
  "f complex_differentiable (at z) \<longleftrightarrow>
         (\<exists>g. (\<forall>w. f(w) - f(z) = g(w) * (w - z)) \<and> continuous (at z) g)"
  using CARAT_DERIV [of f]
  by (simp add: complex_differentiable_def has_field_derivative_def)

lemma complex_differentiable_caratheodory_within:
  "f complex_differentiable (at z within s) \<longleftrightarrow>
         (\<exists>g. (\<forall>w. f(w) - f(z) = g(w) * (w - z)) \<and> continuous (at z within s) g)"
  using DERIV_caratheodory_within [of f]
  by (simp add: complex_differentiable_def has_field_derivative_def)

subsection{*Holomorphic*}

definition holomorphic_on :: "[complex \<Rightarrow> complex, complex set] \<Rightarrow> bool"
           (infixl "(holomorphic'_on)" 50)
  where "f holomorphic_on s \<equiv> \<forall>x\<in>s. f complex_differentiable (at x within s)"
  
lemma holomorphic_on_empty: "f holomorphic_on {}"
  by (simp add: holomorphic_on_def)

lemma holomorphic_on_open:
    "open s \<Longrightarrow> f holomorphic_on s \<longleftrightarrow> (\<forall>x \<in> s. \<exists>f'. DERIV f x :> f')"
  by (auto simp: holomorphic_on_def complex_differentiable_def has_field_derivative_def at_within_open [of _ s])

lemma holomorphic_on_imp_continuous_on: 
    "f holomorphic_on s \<Longrightarrow> continuous_on s f"
  by (metis complex_differentiable_imp_continuous_at continuous_on_eq_continuous_within holomorphic_on_def) 

lemma holomorphic_on_subset:
    "f holomorphic_on s \<Longrightarrow> t \<subseteq> s \<Longrightarrow> f holomorphic_on t"
  unfolding holomorphic_on_def
  by (metis complex_differentiable_within_subset subsetD)

lemma holomorphic_transform: "\<lbrakk>f holomorphic_on s; \<And>x. x \<in> s \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> g holomorphic_on s"
  by (metis complex_differentiable_transform_within linordered_field_no_ub holomorphic_on_def)

lemma holomorphic_cong: "s = t ==> (\<And>x. x \<in> s \<Longrightarrow> f x = g x) \<Longrightarrow> f holomorphic_on s \<longleftrightarrow> g holomorphic_on t"
  by (metis holomorphic_transform)

lemma holomorphic_on_linear: "(op * c) holomorphic_on s"
  unfolding holomorphic_on_def by (metis complex_differentiable_linear)

lemma holomorphic_on_const: "(\<lambda>z. c) holomorphic_on s"
  unfolding holomorphic_on_def by (metis complex_differentiable_const)

lemma holomorphic_on_ident: "(\<lambda>x. x) holomorphic_on s"
  unfolding holomorphic_on_def by (metis complex_differentiable_ident)

lemma holomorphic_on_id: "id holomorphic_on s"
  unfolding id_def by (rule holomorphic_on_ident)

lemma holomorphic_on_compose:
  "f holomorphic_on s \<Longrightarrow> g holomorphic_on (f ` s) \<Longrightarrow> (g o f) holomorphic_on s"
  using complex_differentiable_compose_within[of f _ s g]
  by (auto simp: holomorphic_on_def)

lemma holomorphic_on_compose_gen:
  "f holomorphic_on s \<Longrightarrow> g holomorphic_on t \<Longrightarrow> f ` s \<subseteq> t \<Longrightarrow> (g o f) holomorphic_on s"
  by (metis holomorphic_on_compose holomorphic_on_subset)

lemma holomorphic_on_minus: "f holomorphic_on s \<Longrightarrow> (\<lambda>z. -(f z)) holomorphic_on s"
  by (metis complex_differentiable_minus holomorphic_on_def)

lemma holomorphic_on_add:
  "\<lbrakk>f holomorphic_on s; g holomorphic_on s\<rbrakk> \<Longrightarrow> (\<lambda>z. f z + g z) holomorphic_on s"
  unfolding holomorphic_on_def by (metis complex_differentiable_add)

lemma holomorphic_on_diff:
  "\<lbrakk>f holomorphic_on s; g holomorphic_on s\<rbrakk> \<Longrightarrow> (\<lambda>z. f z - g z) holomorphic_on s"
  unfolding holomorphic_on_def by (metis complex_differentiable_diff)

lemma holomorphic_on_mult:
  "\<lbrakk>f holomorphic_on s; g holomorphic_on s\<rbrakk> \<Longrightarrow> (\<lambda>z. f z * g z) holomorphic_on s"
  unfolding holomorphic_on_def by (metis complex_differentiable_mult)

lemma holomorphic_on_inverse:
  "\<lbrakk>f holomorphic_on s; \<And>z. z \<in> s \<Longrightarrow> f z \<noteq> 0\<rbrakk> \<Longrightarrow> (\<lambda>z. inverse (f z)) holomorphic_on s"
  unfolding holomorphic_on_def by (metis complex_differentiable_inverse)

lemma holomorphic_on_divide:
  "\<lbrakk>f holomorphic_on s; g holomorphic_on s; \<And>z. z \<in> s \<Longrightarrow> g z \<noteq> 0\<rbrakk> \<Longrightarrow> (\<lambda>z. f z / g z) holomorphic_on s"
  unfolding holomorphic_on_def by (metis complex_differentiable_divide)

lemma holomorphic_on_power:
  "f holomorphic_on s \<Longrightarrow> (\<lambda>z. (f z)^n) holomorphic_on s"
  unfolding holomorphic_on_def by (metis complex_differentiable_power)

lemma holomorphic_on_setsum:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i) holomorphic_on s) \<Longrightarrow> (\<lambda>x. setsum (\<lambda>i. f i x) I) holomorphic_on s"
  unfolding holomorphic_on_def by (metis complex_differentiable_setsum)

definition deriv :: "('a \<Rightarrow> 'a::real_normed_field) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "deriv f x \<equiv> THE D. DERIV f x :> D"

lemma DERIV_imp_deriv: "DERIV f x :> f' \<Longrightarrow> deriv f x = f'"
  unfolding deriv_def by (metis the_equality DERIV_unique)

lemma DERIV_deriv_iff_real_differentiable:
  fixes x :: real
  shows "DERIV f x :> deriv f x \<longleftrightarrow> f differentiable at x"
  unfolding differentiable_def by (metis DERIV_imp_deriv has_real_derivative_iff)

lemma real_derivative_chain:
  fixes x :: real
  shows "f differentiable at x \<Longrightarrow> g differentiable at (f x)
    \<Longrightarrow> deriv (g o f) x = deriv g (f x) * deriv f x"
  by (metis DERIV_deriv_iff_real_differentiable DERIV_chain DERIV_imp_deriv)

lemma DERIV_deriv_iff_complex_differentiable:
  "DERIV f x :> deriv f x \<longleftrightarrow> f complex_differentiable at x"
  unfolding complex_differentiable_def by (metis DERIV_imp_deriv)

lemma complex_derivative_chain:
  "f complex_differentiable at x \<Longrightarrow> g complex_differentiable at (f x)
    \<Longrightarrow> deriv (g o f) x = deriv g (f x) * deriv f x"
  by (metis DERIV_deriv_iff_complex_differentiable DERIV_chain DERIV_imp_deriv)

lemma complex_derivative_linear: "deriv (\<lambda>w. c * w) = (\<lambda>z. c)"
  by (metis DERIV_imp_deriv DERIV_cmult_Id)

lemma complex_derivative_ident: "deriv (\<lambda>w. w) = (\<lambda>z. 1)"
  by (metis DERIV_imp_deriv DERIV_ident)

lemma complex_derivative_const: "deriv (\<lambda>w. c) = (\<lambda>z. 0)"
  by (metis DERIV_imp_deriv DERIV_const)

lemma complex_derivative_add:
  "\<lbrakk>f complex_differentiable at z; g complex_differentiable at z\<rbrakk>  
   \<Longrightarrow> deriv (\<lambda>w. f w + g w) z = deriv f z + deriv g z"
  unfolding DERIV_deriv_iff_complex_differentiable[symmetric]
  by (auto intro!: DERIV_imp_deriv derivative_intros)

lemma complex_derivative_diff:
  "\<lbrakk>f complex_differentiable at z; g complex_differentiable at z\<rbrakk>  
   \<Longrightarrow> deriv (\<lambda>w. f w - g w) z = deriv f z - deriv g z"
  unfolding DERIV_deriv_iff_complex_differentiable[symmetric]
  by (auto intro!: DERIV_imp_deriv derivative_intros)

lemma complex_derivative_mult:
  "\<lbrakk>f complex_differentiable at z; g complex_differentiable at z\<rbrakk>  
   \<Longrightarrow> deriv (\<lambda>w. f w * g w) z = f z * deriv g z + deriv f z * g z"
  unfolding DERIV_deriv_iff_complex_differentiable[symmetric]
  by (auto intro!: DERIV_imp_deriv derivative_eq_intros)

lemma complex_derivative_cmult:
  "f complex_differentiable at z \<Longrightarrow> deriv (\<lambda>w. c * f w) z = c * deriv f z"
  unfolding DERIV_deriv_iff_complex_differentiable[symmetric]
  by (auto intro!: DERIV_imp_deriv derivative_eq_intros)

lemma complex_derivative_cmult_right:
  "f complex_differentiable at z \<Longrightarrow> deriv (\<lambda>w. f w * c) z = deriv f z * c"
  unfolding DERIV_deriv_iff_complex_differentiable[symmetric]
  by (auto intro!: DERIV_imp_deriv derivative_eq_intros)

lemma complex_derivative_transform_within_open:
  "\<lbrakk>f holomorphic_on s; g holomorphic_on s; open s; z \<in> s; \<And>w. w \<in> s \<Longrightarrow> f w = g w\<rbrakk> 
   \<Longrightarrow> deriv f z = deriv g z"
  unfolding holomorphic_on_def
  by (rule DERIV_imp_deriv)
     (metis DERIV_deriv_iff_complex_differentiable DERIV_transform_within_open at_within_open)

lemma complex_derivative_compose_linear:
  "f complex_differentiable at (c * z) \<Longrightarrow> deriv (\<lambda>w. f (c * w)) z = c * deriv f (c * z)"
apply (rule DERIV_imp_deriv)
apply (simp add: DERIV_deriv_iff_complex_differentiable [symmetric])
apply (metis DERIV_chain' DERIV_cmult_Id comm_semiring_1_class.normalizing_semiring_rules(7))  
done

subsection{*analyticity on a set*}

definition analytic_on (infixl "(analytic'_on)" 50)  
  where
   "f analytic_on s \<equiv> \<forall>x \<in> s. \<exists>e. 0 < e \<and> f holomorphic_on (ball x e)"

lemma analytic_imp_holomorphic: "f analytic_on s \<Longrightarrow> f holomorphic_on s"
  by (simp add: at_within_open [OF _ open_ball] analytic_on_def holomorphic_on_def)
     (metis centre_in_ball complex_differentiable_at_within)

lemma analytic_on_open: "open s \<Longrightarrow> f analytic_on s \<longleftrightarrow> f holomorphic_on s"
apply (auto simp: analytic_imp_holomorphic)
apply (auto simp: analytic_on_def holomorphic_on_def)
by (metis holomorphic_on_def holomorphic_on_subset open_contains_ball)

lemma analytic_on_imp_differentiable_at:
  "f analytic_on s \<Longrightarrow> x \<in> s \<Longrightarrow> f complex_differentiable (at x)"
 apply (auto simp: analytic_on_def holomorphic_on_def)
by (metis Topology_Euclidean_Space.open_ball centre_in_ball complex_differentiable_within_open)

lemma analytic_on_subset: "f analytic_on s \<Longrightarrow> t \<subseteq> s \<Longrightarrow> f analytic_on t"
  by (auto simp: analytic_on_def)

lemma analytic_on_Un: "f analytic_on (s \<union> t) \<longleftrightarrow> f analytic_on s \<and> f analytic_on t"
  by (auto simp: analytic_on_def)

lemma analytic_on_Union: "f analytic_on (\<Union> s) \<longleftrightarrow> (\<forall>t \<in> s. f analytic_on t)"
  by (auto simp: analytic_on_def)

lemma analytic_on_UN: "f analytic_on (\<Union>i\<in>I. s i) \<longleftrightarrow> (\<forall>i\<in>I. f analytic_on (s i))"
  by (auto simp: analytic_on_def)
  
lemma analytic_on_holomorphic:
  "f analytic_on s \<longleftrightarrow> (\<exists>t. open t \<and> s \<subseteq> t \<and> f holomorphic_on t)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs \<longleftrightarrow> (\<exists>t. open t \<and> s \<subseteq> t \<and> f analytic_on t)"
  proof safe
    assume "f analytic_on s"
    then show "\<exists>t. open t \<and> s \<subseteq> t \<and> f analytic_on t"
      apply (simp add: analytic_on_def)
      apply (rule exI [where x="\<Union>{u. open u \<and> f analytic_on u}"], auto)
      apply (metis Topology_Euclidean_Space.open_ball analytic_on_open centre_in_ball)
      by (metis analytic_on_def)
  next
    fix t
    assume "open t" "s \<subseteq> t" "f analytic_on t" 
    then show "f analytic_on s"
        by (metis analytic_on_subset)
  qed
  also have "... \<longleftrightarrow> ?rhs"
    by (auto simp: analytic_on_open)
  finally show ?thesis .
qed

lemma analytic_on_linear: "(op * c) analytic_on s"
  by (auto simp add: analytic_on_holomorphic holomorphic_on_linear)

lemma analytic_on_const: "(\<lambda>z. c) analytic_on s"
  by (metis analytic_on_def holomorphic_on_const zero_less_one)

lemma analytic_on_ident: "(\<lambda>x. x) analytic_on s"
  by (simp add: analytic_on_def holomorphic_on_ident gt_ex)

lemma analytic_on_id: "id analytic_on s"
  unfolding id_def by (rule analytic_on_ident)

lemma analytic_on_compose:
  assumes f: "f analytic_on s"
      and g: "g analytic_on (f ` s)"
    shows "(g o f) analytic_on s"
unfolding analytic_on_def
proof (intro ballI)
  fix x
  assume x: "x \<in> s"
  then obtain e where e: "0 < e" and fh: "f holomorphic_on ball x e" using f
    by (metis analytic_on_def)
  obtain e' where e': "0 < e'" and gh: "g holomorphic_on ball (f x) e'" using g
    by (metis analytic_on_def g image_eqI x) 
  have "isCont f x"
    by (metis analytic_on_imp_differentiable_at complex_differentiable_imp_continuous_at f x)
  with e' obtain d where d: "0 < d" and fd: "f ` ball x d \<subseteq> ball (f x) e'"
     by (auto simp: continuous_at_ball)
  have "g \<circ> f holomorphic_on ball x (min d e)" 
    apply (rule holomorphic_on_compose)
    apply (metis fh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
    by (metis fd gh holomorphic_on_subset image_mono min.cobounded1 subset_ball)
  then show "\<exists>e>0. g \<circ> f holomorphic_on ball x e"
    by (metis d e min_less_iff_conj) 
qed

lemma analytic_on_compose_gen:
  "f analytic_on s \<Longrightarrow> g analytic_on t \<Longrightarrow> (\<And>z. z \<in> s \<Longrightarrow> f z \<in> t)
             \<Longrightarrow> g o f analytic_on s"
by (metis analytic_on_compose analytic_on_subset image_subset_iff)

lemma analytic_on_neg:
  "f analytic_on s \<Longrightarrow> (\<lambda>z. -(f z)) analytic_on s"
by (metis analytic_on_holomorphic holomorphic_on_minus)

lemma analytic_on_add:
  assumes f: "f analytic_on s"
      and g: "g analytic_on s"
    shows "(\<lambda>z. f z + g z) analytic_on s"
unfolding analytic_on_def
proof (intro ballI)
  fix z
  assume z: "z \<in> s"
  then obtain e where e: "0 < e" and fh: "f holomorphic_on ball z e" using f
    by (metis analytic_on_def)
  obtain e' where e': "0 < e'" and gh: "g holomorphic_on ball z e'" using g
    by (metis analytic_on_def g z) 
  have "(\<lambda>z. f z + g z) holomorphic_on ball z (min e e')" 
    apply (rule holomorphic_on_add) 
    apply (metis fh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
    by (metis gh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
  then show "\<exists>e>0. (\<lambda>z. f z + g z) holomorphic_on ball z e"
    by (metis e e' min_less_iff_conj)
qed

lemma analytic_on_diff:
  assumes f: "f analytic_on s"
      and g: "g analytic_on s"
    shows "(\<lambda>z. f z - g z) analytic_on s"
unfolding analytic_on_def
proof (intro ballI)
  fix z
  assume z: "z \<in> s"
  then obtain e where e: "0 < e" and fh: "f holomorphic_on ball z e" using f
    by (metis analytic_on_def)
  obtain e' where e': "0 < e'" and gh: "g holomorphic_on ball z e'" using g
    by (metis analytic_on_def g z) 
  have "(\<lambda>z. f z - g z) holomorphic_on ball z (min e e')" 
    apply (rule holomorphic_on_diff) 
    apply (metis fh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
    by (metis gh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
  then show "\<exists>e>0. (\<lambda>z. f z - g z) holomorphic_on ball z e"
    by (metis e e' min_less_iff_conj)
qed

lemma analytic_on_mult:
  assumes f: "f analytic_on s"
      and g: "g analytic_on s"
    shows "(\<lambda>z. f z * g z) analytic_on s"
unfolding analytic_on_def
proof (intro ballI)
  fix z
  assume z: "z \<in> s"
  then obtain e where e: "0 < e" and fh: "f holomorphic_on ball z e" using f
    by (metis analytic_on_def)
  obtain e' where e': "0 < e'" and gh: "g holomorphic_on ball z e'" using g
    by (metis analytic_on_def g z) 
  have "(\<lambda>z. f z * g z) holomorphic_on ball z (min e e')" 
    apply (rule holomorphic_on_mult) 
    apply (metis fh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
    by (metis gh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
  then show "\<exists>e>0. (\<lambda>z. f z * g z) holomorphic_on ball z e"
    by (metis e e' min_less_iff_conj)
qed

lemma analytic_on_inverse:
  assumes f: "f analytic_on s"
      and nz: "(\<And>z. z \<in> s \<Longrightarrow> f z \<noteq> 0)"
    shows "(\<lambda>z. inverse (f z)) analytic_on s"
unfolding analytic_on_def
proof (intro ballI)
  fix z
  assume z: "z \<in> s"
  then obtain e where e: "0 < e" and fh: "f holomorphic_on ball z e" using f
    by (metis analytic_on_def)
  have "continuous_on (ball z e) f"
    by (metis fh holomorphic_on_imp_continuous_on)
  then obtain e' where e': "0 < e'" and nz': "\<And>y. dist z y < e' \<Longrightarrow> f y \<noteq> 0" 
    by (metis Topology_Euclidean_Space.open_ball centre_in_ball continuous_on_open_avoid e z nz)  
  have "(\<lambda>z. inverse (f z)) holomorphic_on ball z (min e e')" 
    apply (rule holomorphic_on_inverse)
    apply (metis fh holomorphic_on_subset min.cobounded2 min.commute subset_ball)
    by (metis nz' mem_ball min_less_iff_conj) 
  then show "\<exists>e>0. (\<lambda>z. inverse (f z)) holomorphic_on ball z e"
    by (metis e e' min_less_iff_conj)
qed


lemma analytic_on_divide:
  assumes f: "f analytic_on s"
      and g: "g analytic_on s"
      and nz: "(\<And>z. z \<in> s \<Longrightarrow> g z \<noteq> 0)"
    shows "(\<lambda>z. f z / g z) analytic_on s"
unfolding divide_inverse
by (metis analytic_on_inverse analytic_on_mult f g nz)

lemma analytic_on_power:
  "f analytic_on s \<Longrightarrow> (\<lambda>z. (f z) ^ n) analytic_on s"
by (induct n) (auto simp: analytic_on_const analytic_on_mult)

lemma analytic_on_setsum:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i) analytic_on s) \<Longrightarrow> (\<lambda>x. setsum (\<lambda>i. f i x) I) analytic_on s"
  by (induct I rule: infinite_finite_induct) (auto simp: analytic_on_const analytic_on_add)

subsection{*analyticity at a point.*}

lemma analytic_at_ball:
  "f analytic_on {z} \<longleftrightarrow> (\<exists>e. 0<e \<and> f holomorphic_on ball z e)"
by (metis analytic_on_def singleton_iff)

lemma analytic_at:
    "f analytic_on {z} \<longleftrightarrow> (\<exists>s. open s \<and> z \<in> s \<and> f holomorphic_on s)"
by (metis analytic_on_holomorphic empty_subsetI insert_subset)

lemma analytic_on_analytic_at:
    "f analytic_on s \<longleftrightarrow> (\<forall>z \<in> s. f analytic_on {z})"
by (metis analytic_at_ball analytic_on_def)

lemma analytic_at_two:
  "f analytic_on {z} \<and> g analytic_on {z} \<longleftrightarrow>
   (\<exists>s. open s \<and> z \<in> s \<and> f holomorphic_on s \<and> g holomorphic_on s)"
  (is "?lhs = ?rhs")
proof 
  assume ?lhs
  then obtain s t 
    where st: "open s" "z \<in> s" "f holomorphic_on s"
              "open t" "z \<in> t" "g holomorphic_on t"
    by (auto simp: analytic_at)
  show ?rhs
    apply (rule_tac x="s \<inter> t" in exI)
    using st
    apply (auto simp: Diff_subset holomorphic_on_subset)
    done
next
  assume ?rhs 
  then show ?lhs
    by (force simp add: analytic_at)
qed

subsection{*Combining theorems for derivative with ``analytic at'' hypotheses*}

lemma 
  assumes "f analytic_on {z}" "g analytic_on {z}"
  shows complex_derivative_add_at: "deriv (\<lambda>w. f w + g w) z = deriv f z + deriv g z"
    and complex_derivative_diff_at: "deriv (\<lambda>w. f w - g w) z = deriv f z - deriv g z"
    and complex_derivative_mult_at: "deriv (\<lambda>w. f w * g w) z =
           f z * deriv g z + deriv f z * g z"
proof -
  obtain s where s: "open s" "z \<in> s" "f holomorphic_on s" "g holomorphic_on s"
    using assms by (metis analytic_at_two)
  show "deriv (\<lambda>w. f w + g w) z = deriv f z + deriv g z"
    apply (rule DERIV_imp_deriv [OF DERIV_add])
    using s
    apply (auto simp: holomorphic_on_open complex_differentiable_def DERIV_deriv_iff_complex_differentiable)
    done
  show "deriv (\<lambda>w. f w - g w) z = deriv f z - deriv g z"
    apply (rule DERIV_imp_deriv [OF DERIV_diff])
    using s
    apply (auto simp: holomorphic_on_open complex_differentiable_def DERIV_deriv_iff_complex_differentiable)
    done
  show "deriv (\<lambda>w. f w * g w) z = f z * deriv g z + deriv f z * g z"
    apply (rule DERIV_imp_deriv [OF DERIV_mult'])
    using s
    apply (auto simp: holomorphic_on_open complex_differentiable_def DERIV_deriv_iff_complex_differentiable)
    done
qed

lemma complex_derivative_cmult_at:
  "f analytic_on {z} \<Longrightarrow>  deriv (\<lambda>w. c * f w) z = c * deriv f z"
by (auto simp: complex_derivative_mult_at complex_derivative_const analytic_on_const)

lemma complex_derivative_cmult_right_at:
  "f analytic_on {z} \<Longrightarrow>  deriv (\<lambda>w. f w * c) z = deriv f z * c"
by (auto simp: complex_derivative_mult_at complex_derivative_const analytic_on_const)

subsection{*Complex differentiation of sequences and series*}

lemma has_complex_derivative_sequence:
  fixes s :: "complex set"
  assumes cvs: "convex s"
      and df:  "\<And>n x. x \<in> s \<Longrightarrow> (f n has_field_derivative f' n x) (at x within s)"
      and conv: "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n x. n \<ge> N \<longrightarrow> x \<in> s \<longrightarrow> norm (f' n x - g' x) \<le> e"
      and "\<exists>x l. x \<in> s \<and> ((\<lambda>n. f n x) ---> l) sequentially"
    shows "\<exists>g. \<forall>x \<in> s. ((\<lambda>n. f n x) ---> g x) sequentially \<and> 
                       (g has_field_derivative (g' x)) (at x within s)"
proof -
  from assms obtain x l where x: "x \<in> s" and tf: "((\<lambda>n. f n x) ---> l) sequentially"
    by blast
  { fix e::real assume e: "e > 0"
    then obtain N where N: "\<forall>n\<ge>N. \<forall>x. x \<in> s \<longrightarrow> cmod (f' n x - g' x) \<le> e"
      by (metis conv)    
    have "\<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. cmod (f' n x * h - g' x * h) \<le> e * cmod h"
    proof (rule exI [of _ N], clarify)
      fix n y h
      assume "N \<le> n" "y \<in> s"
      then have "cmod (f' n y - g' y) \<le> e"
        by (metis N)
      then have "cmod h * cmod (f' n y - g' y) \<le> cmod h * e"
        by (auto simp: antisym_conv2 mult_le_cancel_left norm_triangle_ineq2)
      then show "cmod (f' n y * h - g' y * h) \<le> e * cmod h"
        by (simp add: norm_mult [symmetric] field_simps)
    qed
  } note ** = this
  show ?thesis
  unfolding has_field_derivative_def
  proof (rule has_derivative_sequence [OF cvs _ _ x])
    show "\<forall>n. \<forall>x\<in>s. (f n has_derivative (op * (f' n x))) (at x within s)"
      by (metis has_field_derivative_def df)
  next show "(\<lambda>n. f n x) ----> l"
    by (rule tf)
  next show "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. cmod (f' n x * h - g' x * h) \<le> e * cmod h"
    by (blast intro: **)
  qed
qed


lemma has_complex_derivative_series:
  fixes s :: "complex set"
  assumes cvs: "convex s"
      and df:  "\<And>n x. x \<in> s \<Longrightarrow> (f n has_field_derivative f' n x) (at x within s)"
      and conv: "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n x. n \<ge> N \<longrightarrow> x \<in> s 
                \<longrightarrow> cmod ((\<Sum>i<n. f' i x) - g' x) \<le> e"
      and "\<exists>x l. x \<in> s \<and> ((\<lambda>n. f n x) sums l)"
    shows "\<exists>g. \<forall>x \<in> s. ((\<lambda>n. f n x) sums g x) \<and> ((g has_field_derivative g' x) (at x within s))"
proof -
  from assms obtain x l where x: "x \<in> s" and sf: "((\<lambda>n. f n x) sums l)"
    by blast
  { fix e::real assume e: "e > 0"
    then obtain N where N: "\<forall>n x. n \<ge> N \<longrightarrow> x \<in> s 
            \<longrightarrow> cmod ((\<Sum>i<n. f' i x) - g' x) \<le> e"
      by (metis conv)    
    have "\<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. cmod ((\<Sum>i<n. h * f' i x) - g' x * h) \<le> e * cmod h"
    proof (rule exI [of _ N], clarify)
      fix n y h
      assume "N \<le> n" "y \<in> s"
      then have "cmod ((\<Sum>i<n. f' i y) - g' y) \<le> e"
        by (metis N)
      then have "cmod h * cmod ((\<Sum>i<n. f' i y) - g' y) \<le> cmod h * e"
        by (auto simp: antisym_conv2 mult_le_cancel_left norm_triangle_ineq2)
      then show "cmod ((\<Sum>i<n. h * f' i y) - g' y * h) \<le> e * cmod h"
        by (simp add: norm_mult [symmetric] field_simps setsum_right_distrib)
    qed
  } note ** = this
  show ?thesis
  unfolding has_field_derivative_def
  proof (rule has_derivative_series [OF cvs _ _ x])
    fix n x
    assume "x \<in> s"
    then show "((f n) has_derivative (\<lambda>z. z * f' n x)) (at x within s)"
      by (metis df has_field_derivative_def mult_commute_abs)
  next show " ((\<lambda>n. f n x) sums l)"
    by (rule sf)
  next show "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. cmod ((\<Sum>i<n. h * f' i x) - g' x * h) \<le> e * cmod h"
    by (blast intro: **)
  qed
qed

subsection{*Bound theorem*}

lemma complex_differentiable_bound:
  fixes s :: "complex set"
  assumes cvs: "convex s"
      and df:  "\<And>z. z \<in> s \<Longrightarrow> (f has_field_derivative f' z) (at z within s)"
      and dn:  "\<And>z. z \<in> s \<Longrightarrow> norm (f' z) \<le> B"
      and "x \<in> s"  "y \<in> s"
    shows "norm(f x - f y) \<le> B * norm(x - y)"
  apply (rule differentiable_bound [OF cvs])
  apply (rule ballI, erule df [unfolded has_field_derivative_def])
  apply (rule ballI, rule onorm_le, simp add: norm_mult mult_right_mono dn)
  apply fact
  apply fact
  done

subsection{*Inverse function theorem for complex derivatives.*}

lemma has_complex_derivative_inverse_basic:
  fixes f :: "complex \<Rightarrow> complex"
  shows "DERIV f (g y) :> f' \<Longrightarrow>
        f' \<noteq> 0 \<Longrightarrow>
        continuous (at y) g \<Longrightarrow>
        open t \<Longrightarrow>
        y \<in> t \<Longrightarrow>
        (\<And>z. z \<in> t \<Longrightarrow> f (g z) = z)
        \<Longrightarrow> DERIV g y :> inverse (f')"
  unfolding has_field_derivative_def
  apply (rule has_derivative_inverse_basic)
  apply (auto simp:  bounded_linear_mult_right)
  done

(*Used only once, in Multivariate/cauchy.ml. *)
lemma has_complex_derivative_inverse_strong:
  fixes f :: "complex \<Rightarrow> complex"
  shows "DERIV f x :> f' \<Longrightarrow>
         f' \<noteq> 0 \<Longrightarrow>
         open s \<Longrightarrow>
         x \<in> s \<Longrightarrow>
         continuous_on s f \<Longrightarrow>
         (\<And>z. z \<in> s \<Longrightarrow> g (f z) = z)
         \<Longrightarrow> DERIV g (f x) :> inverse (f')"
  unfolding has_field_derivative_def
  apply (rule has_derivative_inverse_strong [of s x f g ])
  using assms 
  by auto

lemma has_complex_derivative_inverse_strong_x:
  fixes f :: "complex \<Rightarrow> complex"
  shows  "DERIV f (g y) :> f' \<Longrightarrow>
          f' \<noteq> 0 \<Longrightarrow>
          open s \<Longrightarrow>
          continuous_on s f \<Longrightarrow>
          g y \<in> s \<Longrightarrow> f(g y) = y \<Longrightarrow>
          (\<And>z. z \<in> s \<Longrightarrow> g (f z) = z)
          \<Longrightarrow> DERIV g y :> inverse (f')"
  unfolding has_field_derivative_def
  apply (rule has_derivative_inverse_strong_x [of s g y f])
  using assms 
  by auto

subsection {* Taylor on Complex Numbers *}

lemma setsum_Suc_reindex:
  fixes f :: "nat \<Rightarrow> 'a::ab_group_add"
    shows  "setsum f {0..n} = f 0 - f (Suc n) + setsum (\<lambda>i. f (Suc i)) {0..n}"
by (induct n) auto

lemma complex_taylor:
  assumes s: "convex s" 
      and f: "\<And>i x. x \<in> s \<Longrightarrow> i \<le> n \<Longrightarrow> (f i has_field_derivative f (Suc i) x) (at x within s)"
      and B: "\<And>x. x \<in> s \<Longrightarrow> cmod (f (Suc n) x) \<le> B"
      and w: "w \<in> s"
      and z: "z \<in> s"
    shows "cmod(f 0 z - (\<Sum>i\<le>n. f i w * (z-w) ^ i / of_nat (fact i)))
          \<le> B * cmod(z - w)^(Suc n) / fact n"
proof -
  have wzs: "closed_segment w z \<subseteq> s" using assms
    by (metis convex_contains_segment)
  { fix u
    assume "u \<in> closed_segment w z"
    then have "u \<in> s"
      by (metis wzs subsetD)
    have "(\<Sum>i\<le>n. f i u * (- of_nat i * (z-u)^(i - 1)) / of_nat (fact i) +
                      f (Suc i) u * (z-u)^i / of_nat (fact i)) = 
              f (Suc n) u * (z-u) ^ n / of_nat (fact n)"
    proof (induction n)
      case 0 show ?case by simp
    next
      case (Suc n)
      have "(\<Sum>i\<le>Suc n. f i u * (- of_nat i * (z-u) ^ (i - 1)) / of_nat (fact i) +
                             f (Suc i) u * (z-u) ^ i / of_nat (fact i)) =  
           f (Suc n) u * (z-u) ^ n / of_nat (fact n) +
           f (Suc (Suc n)) u * ((z-u) * (z-u) ^ n) / of_nat (fact (Suc n)) -
           f (Suc n) u * ((1 + of_nat n) * (z-u) ^ n) / of_nat (fact (Suc n))"
        using Suc by simp
      also have "... = f (Suc (Suc n)) u * (z-u) ^ Suc n / of_nat (fact (Suc n))"
      proof -
        have "of_nat(fact(Suc n)) *
             (f(Suc n) u *(z-u) ^ n / of_nat(fact n) +
               f(Suc(Suc n)) u *((z-u) *(z-u) ^ n) / of_nat(fact(Suc n)) -
               f(Suc n) u *((1 + of_nat n) *(z-u) ^ n) / of_nat(fact(Suc n))) =
            (of_nat(fact(Suc n)) *(f(Suc n) u *(z-u) ^ n)) / of_nat(fact n) +
            (of_nat(fact(Suc n)) *(f(Suc(Suc n)) u *((z-u) *(z-u) ^ n)) / of_nat(fact(Suc n))) -
            (of_nat(fact(Suc n)) *(f(Suc n) u *(of_nat(Suc n) *(z-u) ^ n))) / of_nat(fact(Suc n))"
          by (simp add: algebra_simps del: fact_Suc)
        also have "... =
                   (of_nat (fact (Suc n)) * (f (Suc n) u * (z-u) ^ n)) / of_nat (fact n) +
                   (f (Suc (Suc n)) u * ((z-u) * (z-u) ^ n)) -
                   (f (Suc n) u * ((1 + of_nat n) * (z-u) ^ n))"
          by (simp del: fact_Suc)
        also have "... = 
                   (of_nat (Suc n) * (f (Suc n) u * (z-u) ^ n)) +
                   (f (Suc (Suc n)) u * ((z-u) * (z-u) ^ n)) -
                   (f (Suc n) u * ((1 + of_nat n) * (z-u) ^ n))"
          by (simp only: fact_Suc of_nat_mult mult_ac) simp
        also have "... = f (Suc (Suc n)) u * ((z-u) * (z-u) ^ n)"
          by (simp add: algebra_simps)
        finally show ?thesis
        by (simp add: mult_left_cancel [where c = "of_nat (fact (Suc n))", THEN iffD1] del: fact_Suc)
      qed
      finally show ?case .
    qed
    then have "((\<lambda>v. (\<Sum>i\<le>n. f i v * (z - v)^i / of_nat (fact i))) 
                has_field_derivative f (Suc n) u * (z-u) ^ n / of_nat (fact n))
               (at u within s)"
      apply (intro derivative_eq_intros)
      apply (blast intro: assms `u \<in> s`)
      apply (rule refl)+
      apply (auto simp: field_simps)
      done
  } note sum_deriv = this
  { fix u
    assume u: "u \<in> closed_segment w z"
    then have us: "u \<in> s"
      by (metis wzs subsetD)
    have "cmod (f (Suc n) u) * cmod (z - u) ^ n \<le> cmod (f (Suc n) u) * cmod (u - z) ^ n"
      by (metis norm_minus_commute order_refl)
    also have "... \<le> cmod (f (Suc n) u) * cmod (z - w) ^ n"
      by (metis mult_left_mono norm_ge_zero power_mono segment_bound [OF u])
    also have "... \<le> B * cmod (z - w) ^ n"
      by (metis norm_ge_zero zero_le_power mult_right_mono  B [OF us])
    finally have "cmod (f (Suc n) u) * cmod (z - u) ^ n \<le> B * cmod (z - w) ^ n" .
  } note cmod_bound = this
  have "(\<Sum>i\<le>n. f i z * (z - z) ^ i / of_nat (fact i)) = (\<Sum>i\<le>n. (f i z / of_nat (fact i)) * 0 ^ i)"
    by simp
  also have "\<dots> = f 0 z / of_nat (fact 0)"
    by (subst setsum_zero_power) simp
  finally have "cmod (f 0 z - (\<Sum>i\<le>n. f i w * (z - w) ^ i / of_nat (fact i))) 
            \<le> cmod ((\<Sum>i\<le>n. f i w * (z - w) ^ i / of_nat (fact i)) -
                    (\<Sum>i\<le>n. f i z * (z - z) ^ i / of_nat (fact i)))"
    by (simp add: norm_minus_commute)
  also have "... \<le> B * cmod (z - w) ^ n / real_of_nat (fact n) * cmod (w - z)"
    apply (rule complex_differentiable_bound 
      [where f' = "\<lambda>w. f (Suc n) w * (z - w)^n / of_nat(fact n)"
         and s = "closed_segment w z", OF convex_segment])
    apply (auto simp: ends_in_segment real_of_nat_def DERIV_subset [OF sum_deriv wzs]
                  norm_divide norm_mult norm_power divide_le_cancel cmod_bound)
    done
  also have "...  \<le> B * cmod (z - w) ^ Suc n / real (fact n)"
    by (simp add: algebra_simps norm_minus_commute real_of_nat_def)
  finally show ?thesis .
qed

text{* Something more like the traditional MVT for real components.*}

lemma complex_mvt_line:
  assumes "\<And>u. u \<in> closed_segment w z \<Longrightarrow> (f has_field_derivative f'(u)) (at u)"
    shows "\<exists>u. u \<in> open_segment w z \<and> Re(f z) - Re(f w) = Re(f'(u) * (z - w))"
proof -
  have twz: "\<And>t. (1 - t) *\<^sub>R w + t *\<^sub>R z = w + t *\<^sub>R (z - w)"
    by (simp add: real_vector.scale_left_diff_distrib real_vector.scale_right_diff_distrib)
  note assms[unfolded has_field_derivative_def, derivative_intros]
  show ?thesis
    apply (cut_tac mvt_simple
                     [of 0 1 "Re o f o (\<lambda>t. (1 - t) *\<^sub>R w +  t *\<^sub>R z)"
                      "\<lambda>u. Re o (\<lambda>h. f'((1 - u) *\<^sub>R w + u *\<^sub>R z) * h) o (\<lambda>t. t *\<^sub>R (z - w))"])
    apply auto
    apply (rule_tac x="(1 - x) *\<^sub>R w + x *\<^sub>R z" in exI)
    apply (auto simp add: open_segment_def twz) []
    apply (intro derivative_eq_intros has_derivative_at_within)
    apply simp_all
    apply (simp add: fun_eq_iff real_vector.scale_right_diff_distrib)
    apply (force simp add: twz closed_segment_def)
    done
qed

lemma complex_taylor_mvt:
  assumes "\<And>i x. \<lbrakk>x \<in> closed_segment w z; i \<le> n\<rbrakk> \<Longrightarrow> ((f i) has_field_derivative f (Suc i) x) (at x)"
    shows "\<exists>u. u \<in> closed_segment w z \<and>
            Re (f 0 z) =
            Re ((\<Sum>i = 0..n. f i w * (z - w) ^ i / of_nat (fact i)) +
                (f (Suc n) u * (z-u)^n / of_nat (fact n)) * (z - w))"
proof -
  { fix u
    assume u: "u \<in> closed_segment w z"
    have "(\<Sum>i = 0..n.
               (f (Suc i) u * (z-u) ^ i - of_nat i * (f i u * (z-u) ^ (i - Suc 0))) /
               of_nat (fact i)) =
          f (Suc 0) u -
             (f (Suc (Suc n)) u * ((z-u) ^ Suc n) - (of_nat (Suc n)) * (z-u) ^ n * f (Suc n) u) /
             of_nat (fact (Suc n)) +
             (\<Sum>i = 0..n.
                 (f (Suc (Suc i)) u * ((z-u) ^ Suc i) - of_nat (Suc i) * (f (Suc i) u * (z-u) ^ i)) /
                 of_nat (fact (Suc i)))"
       by (subst setsum_Suc_reindex) simp
    also have "... = f (Suc 0) u -
             (f (Suc (Suc n)) u * ((z-u) ^ Suc n) - (of_nat (Suc n)) * (z-u) ^ n * f (Suc n) u) /
             of_nat (fact (Suc n)) +
             (\<Sum>i = 0..n.
                 f (Suc (Suc i)) u * ((z-u) ^ Suc i) / of_nat (fact (Suc i))  - 
                 f (Suc i) u * (z-u) ^ i / of_nat (fact i))"
      by (simp only: diff_divide_distrib fact_cancel mult_ac)
    also have "... = f (Suc 0) u -
             (f (Suc (Suc n)) u * (z-u) ^ Suc n - of_nat (Suc n) * (z-u) ^ n * f (Suc n) u) /
             of_nat (fact (Suc n)) +
             f (Suc (Suc n)) u * (z-u) ^ Suc n / of_nat (fact (Suc n)) - f (Suc 0) u"
      by (subst setsum_Suc_diff) auto
    also have "... = f (Suc n) u * (z-u) ^ n / of_nat (fact n)"
      by (simp only: algebra_simps diff_divide_distrib fact_cancel)
    finally have "(\<Sum>i = 0..n. (f (Suc i) u * (z - u) ^ i 
                             - of_nat i * (f i u * (z-u) ^ (i - Suc 0))) / of_nat (fact i)) =
                  f (Suc n) u * (z - u) ^ n / of_nat (fact n)" .
    then have "((\<lambda>u. \<Sum>i = 0..n. f i u * (z - u) ^ i / of_nat (fact i)) has_field_derivative
                f (Suc n) u * (z - u) ^ n / of_nat (fact n))  (at u)"
      apply (intro derivative_eq_intros)+
      apply (force intro: u assms)
      apply (rule refl)+
      apply (auto simp: mult_ac)
      done
  }
  then show ?thesis
    apply (cut_tac complex_mvt_line [of w z "\<lambda>u. \<Sum>i = 0..n. f i u * (z-u) ^ i / of_nat (fact i)"
               "\<lambda>u. (f (Suc n) u * (z-u)^n / of_nat (fact n))"])
    apply (auto simp add: intro: open_closed_segment)
    done
qed

end
