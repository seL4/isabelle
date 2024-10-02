(*  Title:      HOL/Computational_Algebra/Polynomial_FPS.thy
    Author:     Manuel Eberl, TU München
*)

section \<open>Converting polynomials to formal power series\<close>

theory Polynomial_FPS
  imports Polynomial Formal_Power_Series
begin

context
  includes fps_syntax
begin

definition fps_of_poly where
  "fps_of_poly p = Abs_fps (coeff p)"

lemma fps_of_poly_eq_iff: "fps_of_poly p = fps_of_poly q \<longleftrightarrow> p = q"
  by (simp add: fps_of_poly_def poly_eq_iff fps_eq_iff)

lemma fps_of_poly_nth [simp]: "fps_of_poly p $ n = coeff p n"
  by (simp add: fps_of_poly_def)
  
lemma fps_of_poly_const: "fps_of_poly [:c:] = fps_const c"
proof (subst fps_eq_iff, clarify)
  fix n :: nat show "fps_of_poly [:c:] $ n = fps_const c $ n"
    by (cases n) (auto simp: fps_of_poly_def)
qed

lemma fps_of_poly_0 [simp]: "fps_of_poly 0 = 0"
  by (subst fps_const_0_eq_0 [symmetric], subst fps_of_poly_const [symmetric]) simp

lemma fps_of_poly_1 [simp]: "fps_of_poly 1 = 1"
  by (simp add: fps_eq_iff)

lemma fps_of_poly_1' [simp]: "fps_of_poly [:1:] = 1"
  by (subst fps_const_1_eq_1 [symmetric], subst fps_of_poly_const [symmetric])
     (simp add: one_poly_def)

lemma fps_of_poly_numeral [simp]: "fps_of_poly (numeral n) = numeral n"
  by (simp add: numeral_fps_const fps_of_poly_const [symmetric] numeral_poly)

lemma fps_of_poly_numeral' [simp]: "fps_of_poly [:numeral n:] = numeral n"
  by (simp add: numeral_fps_const fps_of_poly_const [symmetric] numeral_poly)

lemma fps_of_poly_fps_X [simp]: "fps_of_poly [:0, 1:] = fps_X"
  by (auto simp add: fps_of_poly_def fps_eq_iff coeff_pCons split: nat.split)

lemma fps_of_poly_add: "fps_of_poly (p + q) = fps_of_poly p + fps_of_poly q"
  by (simp add: fps_of_poly_def plus_poly.rep_eq fps_plus_def)

lemma fps_of_poly_diff: "fps_of_poly (p - q) = fps_of_poly p - fps_of_poly q"
  by (simp add: fps_of_poly_def minus_poly.rep_eq fps_minus_def)

lemma fps_of_poly_uminus: "fps_of_poly (-p) = -fps_of_poly p"
  by (simp add: fps_of_poly_def uminus_poly.rep_eq fps_uminus_def)

lemma fps_of_poly_mult: "fps_of_poly (p * q) = fps_of_poly p * fps_of_poly q"
  by (simp add: fps_of_poly_def fps_times_def fps_eq_iff coeff_mult atLeast0AtMost)

lemma fps_of_poly_smult: 
  "fps_of_poly (smult c p) = fps_const c * fps_of_poly p"
  using fps_of_poly_mult[of "[:c:]" p] by (simp add: fps_of_poly_mult fps_of_poly_const)
  
lemma fps_of_poly_sum: "fps_of_poly (sum f A) = sum (\<lambda>x. fps_of_poly (f x)) A"
  by (cases "finite A", induction rule: finite_induct) (simp_all add: fps_of_poly_add)

lemma fps_of_poly_sum_list: "fps_of_poly (sum_list xs) = sum_list (map fps_of_poly xs)"
  by (induction xs) (simp_all add: fps_of_poly_add)
  
lemma fps_of_poly_prod: "fps_of_poly (prod f A) = prod (\<lambda>x. fps_of_poly (f x)) A"
  by (cases "finite A", induction rule: finite_induct) (simp_all add: fps_of_poly_mult)
  
lemma fps_of_poly_prod_list: "fps_of_poly (prod_list xs) = prod_list (map fps_of_poly xs)"
  by (induction xs) (simp_all add: fps_of_poly_mult)

lemma fps_of_poly_pCons: 
  "fps_of_poly (pCons (c :: 'a :: semiring_1) p) = fps_const c + fps_of_poly p * fps_X"
  by (subst fps_mult_fps_X_commute [symmetric], intro fps_ext) 
     (auto simp: fps_of_poly_def coeff_pCons split: nat.split)
  
lemma fps_of_poly_pderiv: "fps_of_poly (pderiv p) = fps_deriv (fps_of_poly p)"
  by (intro fps_ext) (simp add: fps_of_poly_nth coeff_pderiv)

lemma fps_of_poly_power: "fps_of_poly (p ^ n) = fps_of_poly p ^ n"
  by (induction n) (simp_all add: fps_of_poly_mult)
  
lemma fps_of_poly_monom: "fps_of_poly (monom (c :: 'a :: comm_ring_1) n) = fps_const c * fps_X ^ n"
  by (intro fps_ext) simp_all

lemma fps_of_poly_monom': "fps_of_poly (monom (1 :: 'a :: comm_ring_1) n) = fps_X ^ n"
  by (simp add: fps_of_poly_monom)

lemma fps_of_poly_div:
  assumes "(q :: 'a :: field poly) dvd p"
  shows   "fps_of_poly (p div q) = fps_of_poly p / fps_of_poly q"
proof (cases "q = 0")
  case False
  from False fps_of_poly_eq_iff[of q 0] have nz: "fps_of_poly q \<noteq> 0" by simp 
  from assms have "p = (p div q) * q" by simp
  also have "fps_of_poly \<dots> = fps_of_poly (p div q) * fps_of_poly q" 
    by (simp add: fps_of_poly_mult)
  also from nz have "\<dots> / fps_of_poly q = fps_of_poly (p div q)"
    by (intro nonzero_mult_div_cancel_right) (auto simp: fps_of_poly_0)
  finally show ?thesis ..
qed simp

lemma fps_of_poly_divide_numeral:
  "fps_of_poly (smult (inverse (numeral c :: 'a :: field)) p) = fps_of_poly p / numeral c"
proof -
  have "smult (inverse (numeral c)) p = [:inverse (numeral c):] * p" by simp
  also have "fps_of_poly \<dots> = fps_of_poly p / numeral c"
    by (subst fps_of_poly_mult) (simp add: numeral_fps_const fps_of_poly_pCons)
  finally show ?thesis by simp
qed


lemma subdegree_fps_of_poly:
  assumes "p \<noteq> 0"
  defines "n \<equiv> Polynomial.order 0 p"
  shows   "subdegree (fps_of_poly p) = n"
proof (rule subdegreeI)
  from assms have "monom 1 n dvd p" by (simp add: monom_1_dvd_iff)
  thus zero: "fps_of_poly p $ i = 0" if "i < n" for i
    using that by (simp add: monom_1_dvd_iff')
    
  from assms have "\<not>monom 1 (Suc n) dvd p"
    by (auto simp: monom_1_dvd_iff simp del: power_Suc)
  then obtain k where k: "k \<le> n" "fps_of_poly p $ k \<noteq> 0" 
    by (auto simp: monom_1_dvd_iff' less_Suc_eq_le)
  with zero[of k] have "k = n" by linarith
  with k show "fps_of_poly p $ n \<noteq> 0" by simp
qed

lemma fps_of_poly_dvd:
  assumes "p dvd q"
  shows   "fps_of_poly (p :: 'a :: field poly) dvd fps_of_poly q"
proof (cases "p = 0 \<or> q = 0")
  case False
  with assms fps_of_poly_eq_iff[of p 0] fps_of_poly_eq_iff[of q 0] show ?thesis
    by (auto simp: fps_dvd_iff subdegree_fps_of_poly dvd_imp_order_le)
qed (insert assms, auto)


lemmas fps_of_poly_simps =
  fps_of_poly_0 fps_of_poly_1 fps_of_poly_numeral fps_of_poly_const fps_of_poly_fps_X
  fps_of_poly_add fps_of_poly_diff fps_of_poly_uminus fps_of_poly_mult fps_of_poly_smult
  fps_of_poly_sum fps_of_poly_sum_list fps_of_poly_prod fps_of_poly_prod_list
  fps_of_poly_pCons fps_of_poly_pderiv fps_of_poly_power fps_of_poly_monom
  fps_of_poly_divide_numeral

lemma fps_of_poly_pcompose:
  assumes "coeff q 0 = (0 :: 'a :: idom)"
  shows   "fps_of_poly (pcompose p q) = fps_compose (fps_of_poly p) (fps_of_poly q)"
  using assms by (induction p rule: pCons_induct)
                 (auto simp: pcompose_pCons fps_of_poly_simps fps_of_poly_pCons 
                             fps_compose_add_distrib fps_compose_mult_distrib)
  
lemmas reify_fps_atom =
  fps_of_poly_0 fps_of_poly_1' fps_of_poly_numeral' fps_of_poly_const fps_of_poly_fps_X


text \<open>
  The following simproc can reduce the equality of two polynomial FPSs two equality of the
  respective polynomials. A polynomial FPS is one that only has finitely many non-zero 
  coefficients and can therefore be written as \<^term>\<open>fps_of_poly p\<close> for some 
  polynomial \<open>p\<close>.
  
  This may sound trivial, but it covers a number of annoying side conditions like 
  \<^term>\<open>1 + fps_X \<noteq> 0\<close> that would otherwise not be solved automatically.
\<close>

ML \<open>

(* TODO: Support for division *)
signature POLY_FPS = sig

val reify_conv : conv
val eq_conv : conv
val eq_simproc : cterm -> thm option

end


structure Poly_Fps = struct

fun const_binop_conv s conv ct =
  case Thm.term_of ct of
    (Const (s', _) $ _ $ _) => 
      if s = s' then 
        Conv.binop_conv conv ct 
      else 
        raise CTERM ("const_binop_conv", [ct])
  | _ => raise CTERM ("const_binop_conv", [ct])

fun reify_conv ct = 
  let
    val rewr = Conv.rewrs_conv o map (fn thm => thm RS @{thm eq_reflection})
    val un = Conv.arg_conv reify_conv
    val bin = Conv.binop_conv reify_conv
  in
    case Thm.term_of ct of
      (Const (\<^const_name>\<open>fps_of_poly\<close>, _) $ _) => ct |> Conv.all_conv
    | (Const (\<^const_name>\<open>Groups.plus\<close>, _) $ _ $ _) => ct |> (
        bin then_conv rewr @{thms fps_of_poly_add [symmetric]})
    | (Const (\<^const_name>\<open>Groups.uminus\<close>, _) $ _) => ct |> (
        un then_conv rewr @{thms fps_of_poly_uminus [symmetric]})
    | (Const (\<^const_name>\<open>Groups.minus\<close>, _) $ _ $ _) => ct |> (
        bin then_conv rewr @{thms fps_of_poly_diff [symmetric]})
    | (Const (\<^const_name>\<open>Groups.times\<close>, _) $ _ $ _) => ct |> (
        bin then_conv rewr @{thms fps_of_poly_mult [symmetric]})
    | (Const (\<^const_name>\<open>Rings.divide\<close>, _) $ _ $ (Const (\<^const_name>\<open>Num.numeral\<close>, _) $ _))
        => ct |> (Conv.fun_conv (Conv.arg_conv reify_conv)
             then_conv rewr @{thms fps_of_poly_divide_numeral [symmetric]})
    | (Const (\<^const_name>\<open>Power.power\<close>, _) $ Const (\<^const_name>\<open>fps_X\<close>,_) $ _) => ct |> (
        rewr @{thms fps_of_poly_monom' [symmetric]}) 
    | (Const (\<^const_name>\<open>Power.power\<close>, _) $ _ $ _) => ct |> (
        Conv.fun_conv (Conv.arg_conv reify_conv) 
        then_conv rewr @{thms fps_of_poly_power [symmetric]})
    | _ => ct |> (
        rewr @{thms reify_fps_atom [symmetric]})
  end
    

fun eq_conv ct =
  case Thm.term_of ct of
    (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _) => ct |> (
      Conv.binop_conv reify_conv
      then_conv Conv.rewr_conv @{thm fps_of_poly_eq_iff[THEN eq_reflection]})
  | _ => raise CTERM ("poly_fps_eq_conv", [ct])

val eq_simproc = try eq_conv

end
\<close> 

simproc_setup poly_fps_eq ("(f :: 'a fps) = g") = \<open>K (K Poly_Fps.eq_simproc)\<close>

lemma fps_of_poly_linear: "fps_of_poly [:a,1 :: 'a :: field:] = fps_X + fps_const a"
  by simp

lemma fps_of_poly_linear': "fps_of_poly [:1,a :: 'a :: field:] = 1 + fps_const a * fps_X"
  by simp

lemma fps_of_poly_cutoff [simp]: 
  "fps_of_poly (poly_cutoff n p) = fps_cutoff n (fps_of_poly p)"
  by (simp add: fps_eq_iff coeff_poly_cutoff)

lemma fps_of_poly_shift [simp]: "fps_of_poly (poly_shift n p) = fps_shift n (fps_of_poly p)"
  by (simp add: fps_eq_iff coeff_poly_shift)


definition poly_subdegree :: "'a::zero poly \<Rightarrow> nat" where
  "poly_subdegree p = subdegree (fps_of_poly p)"

lemma coeff_less_poly_subdegree:
  "k < poly_subdegree p \<Longrightarrow> coeff p k = 0"
  unfolding poly_subdegree_def using nth_less_subdegree_zero[of k "fps_of_poly p"] by simp

(* TODO: Move ? *)
definition prefix_length :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "prefix_length P xs = length (takeWhile P xs)"

primrec prefix_length_aux :: "('a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "prefix_length_aux P acc [] = acc"
| "prefix_length_aux P acc (x#xs) = (if P x then prefix_length_aux P (Suc acc) xs else acc)"

lemma prefix_length_aux_correct: "prefix_length_aux P acc xs = prefix_length P xs + acc"
  by (induction xs arbitrary: acc) (simp_all add: prefix_length_def)

lemma prefix_length_code [code]: "prefix_length P xs = prefix_length_aux P 0 xs"
  by (simp add: prefix_length_aux_correct)

lemma prefix_length_le_length: "prefix_length P xs \<le> length xs"
  by (induction xs) (simp_all add: prefix_length_def)
  
lemma prefix_length_less_length: "(\<exists>x\<in>set xs. \<not>P x) \<Longrightarrow> prefix_length P xs < length xs"
  by (induction xs) (simp_all add: prefix_length_def)

lemma nth_prefix_length:
  "(\<exists>x\<in>set xs. \<not>P x) \<Longrightarrow> \<not>P (xs ! prefix_length P xs)"
  by (induction xs) (simp_all add: prefix_length_def)
  
lemma nth_less_prefix_length:
  "n < prefix_length P xs \<Longrightarrow> P (xs ! n)"
  by (induction xs arbitrary: n) 
     (auto simp: prefix_length_def nth_Cons split: if_splits nat.splits)
(* END TODO *)
  
lemma poly_subdegree_code [code]: "poly_subdegree p = prefix_length ((=) 0) (coeffs p)"
proof (cases "p = 0")
  case False
  note [simp] = this
  define n where "n = prefix_length ((=) 0) (coeffs p)"
  from False have "\<exists>k. coeff p k \<noteq> 0" by (auto simp: poly_eq_iff)
  hence ex: "\<exists>x\<in>set (coeffs p). x \<noteq> 0" by (auto simp: coeffs_def)
  hence n_less: "n < length (coeffs p)" and nonzero: "coeffs p ! n \<noteq> 0" 
    unfolding n_def by (auto intro!: prefix_length_less_length nth_prefix_length)
  show ?thesis unfolding poly_subdegree_def
  proof (intro subdegreeI)
    from n_less have "fps_of_poly p $ n = coeffs p ! n"
      by (subst coeffs_nth) (simp_all add: degree_eq_length_coeffs)
    with nonzero show "fps_of_poly p $ prefix_length ((=) 0) (coeffs p) \<noteq> 0"
      unfolding n_def by simp
  next
    fix k assume A: "k < prefix_length ((=) 0) (coeffs p)"
    also have "\<dots> \<le> length (coeffs p)" by (rule prefix_length_le_length)
    finally show "fps_of_poly p $ k = 0"
      using nth_less_prefix_length[OF A]
      by (simp add: coeffs_nth degree_eq_length_coeffs)
  qed
qed (simp_all add: poly_subdegree_def prefix_length_def)

end

end
