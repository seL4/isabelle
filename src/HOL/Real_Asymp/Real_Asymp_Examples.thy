section \<open>Examples for the \<open>real_asymp\<close> method\<close>
theory Real_Asymp_Examples
  imports Real_Asymp
begin

context
  includes asymp_equiv_syntax
begin

subsection \<open>Dominik Gruntz's examples\<close>

lemma "((\<lambda>x::real. exp x * (exp (1/x - exp (-x)) - exp (1/x))) \<longlongrightarrow> -1) at_top"
  by real_asymp
  
lemma "((\<lambda>x::real. exp x * (exp (1/x + exp (-x) + exp (-(x^2))) -
                     exp (1/x - exp (-exp x)))) \<longlongrightarrow> 1) at_top"
  by real_asymp
  
lemma "filterlim (\<lambda>x::real. exp (exp (x - exp (-x)) / (1 - 1/x)) - exp (exp x)) at_top at_top"
  by real_asymp

text \<open>This example is notable because it produces an expansion of level 9.\<close>
lemma "filterlim (\<lambda>x::real. exp (exp (exp x / (1 - 1/x))) - 
                    exp (exp (exp x / (1 - 1/x - ln x powr (-ln x))))) at_bot at_top"
  by real_asymp

lemma "filterlim (\<lambda>x::real. exp (exp (exp (x + exp (-x)))) / exp (exp (exp x))) at_top at_top"
  by real_asymp

lemma "filterlim (\<lambda>x::real. exp (exp (exp x)) / (exp (exp (exp (x - exp (-exp x)))))) at_top at_top"
  by real_asymp

lemma "((\<lambda>x::real. exp (exp (exp x)) / exp (exp (exp x - exp (-exp (exp x))))) \<longlongrightarrow> 1) at_top"
  by real_asymp

lemma "((\<lambda>x::real. exp (exp x) / exp (exp x - exp (-exp (exp x)))) \<longlongrightarrow> 1) at_top"
  by real_asymp

lemma "filterlim (\<lambda>x::real. ln x ^ 2 * exp (sqrt (ln x) * ln (ln x) ^ 2 * 
         exp (sqrt (ln (ln x)) * ln (ln (ln x)) ^ 3)) / sqrt x) (at_right 0) at_top"
  by real_asymp

lemma "((\<lambda>x::real. (x * ln x * ln (x * exp x - x^2) ^ 2) / 
                    ln (ln (x^2 + 2*exp (exp (3*x^3*ln x))))) \<longlongrightarrow> 1/3) at_top"
  by real_asymp

lemma "((\<lambda>x::real. (exp (x * exp (-x) / (exp (-x) + exp (-(2*x^2)/(x+1)))) - exp x) / x)
          \<longlongrightarrow> -exp 2) at_top"
  by real_asymp
  
lemma "((\<lambda>x::real. (3 powr x + 5 powr x) powr (1/x)) \<longlongrightarrow> 5) at_top"
  by real_asymp
 
lemma "filterlim (\<lambda>x::real. x / (ln (x powr (ln x powr (ln 2 / ln x))))) at_top at_top"
  by real_asymp

lemma "filterlim (\<lambda>x::real. exp (exp (2*ln (x^5 + x) * ln (ln x))) / 
                     exp (exp (10*ln x * ln (ln x)))) at_top at_top"
  by real_asymp

lemma "filterlim (\<lambda>x::real. 4/9 * (exp (exp (5/2*x powr (-5/7) + 21/8*x powr (6/11) + 
              2*x powr (-8) + 54/17*x powr (49/45))) ^ 8) / (ln (ln (-ln (4/3*x powr (-5/14))))))
         at_top at_top"
  by real_asymp

lemma "((\<lambda>x::real. (exp (4*x*exp (-x) / 
                    (1/exp x + 1/exp (2*x^2/(x+1)))) - exp x) / ((exp x)^4)) \<longlongrightarrow> 1) at_top "
  by real_asymp

lemma "((\<lambda>x::real. exp (x*exp (-x) / (exp (-x) + exp (-2*x^2/(x+1))))/exp x) \<longlongrightarrow> 1) at_top"
  by real_asymp

lemma "((\<lambda>x::real. exp (exp (-x/(1+exp (-x)))) * exp (-x/(1+exp (-x/(1+exp (-x))))) * 
           exp (exp (-x+exp (-x/(1+exp (-x))))) / (exp (-x/(1+exp (-x))))^2 - exp x + x) 
         \<longlongrightarrow> 2) at_top"
  by real_asymp

lemma "((\<lambda>x::real. (ln(ln x + ln (ln x)) - ln (ln x)) / 
                      (ln (ln x + ln (ln (ln x)))) * ln x) \<longlongrightarrow> 1) at_top"
  by real_asymp
  
lemma "((\<lambda>x::real. exp (ln (ln (x + exp (ln x * ln (ln x)))) / 
                       (ln (ln (ln (exp x + x + ln x)))))) \<longlongrightarrow> exp 1) at_top"
  by real_asymp

lemma "((\<lambda>x::real. exp x * (sin (1/x + exp (-x)) - sin (1/x + exp (-(x^2))))) \<longlongrightarrow> 1) at_top"
  by real_asymp

lemma "((\<lambda>x::real. exp (exp x) * (exp (sin (1/x + exp (-exp x))) - exp (sin (1/x)))) \<longlongrightarrow> 1) at_top"
  by real_asymp

lemma "((\<lambda>x::real. max x (exp x) / ln (min (exp (-x)) (exp (-exp x)))) \<longlongrightarrow> -1) at_top"
  by real_asymp

text \<open>The following example is taken from the paper by Richardson \<^emph>\<open>et al\<close>.\<close>
lemma 
  defines "f \<equiv> (\<lambda>x::real. ln (ln (x * exp (x * exp x) + 1)) - exp (exp (ln (ln x) + 1 / x)))"
  shows   "(f \<longlongrightarrow> 0) at_top" (is ?thesis1)
          "f \<sim> (\<lambda>x. -(ln x ^ 2) / (2*x))" (is ?thesis2)
  unfolding f_def by real_asymp+

  
subsection \<open>Asymptotic inequalities related to the Akra--Bazzi theorem\<close>
  
definition "akra_bazzi_asymptotic1 b hb e p x \<longleftrightarrow>
  (1 - hb * inverse b * ln x powr -(1+e)) powr p * (1 + ln (b*x + hb*x/ln x powr (1+e)) powr (-e/2))
  \<ge> 1 + (ln x powr (-e/2) :: real)"
definition "akra_bazzi_asymptotic1' b hb e p x \<longleftrightarrow>
  (1 + hb * inverse b * ln x powr -(1+e)) powr p * (1 + ln (b*x + hb*x/ln x powr (1+e)) powr (-e/2))
  \<ge> 1 + (ln x powr (-e/2) :: real)"
definition "akra_bazzi_asymptotic2 b hb e p x \<longleftrightarrow>
  (1 + hb * inverse b * ln x powr -(1+e)) powr p * (1 - ln (b*x + hb*x/ln x powr (1+e)) powr (-e/2))
      \<le> 1 - ln x powr (-e/2 :: real)"
definition "akra_bazzi_asymptotic2' b hb e p x \<longleftrightarrow>
  (1 - hb * inverse b * ln x powr -(1+e)) powr p * (1 - ln (b*x + hb*x/ln x powr (1+e)) powr (-e/2))
      \<le> 1 - ln x powr (-e/2 :: real)"
definition "akra_bazzi_asymptotic3 e x \<longleftrightarrow> (1 + (ln x powr (-e/2))) / 2 \<le> (1::real)"
definition "akra_bazzi_asymptotic4 e x \<longleftrightarrow> (1 - (ln x powr (-e/2))) * 2 \<ge> (1::real)"
definition "akra_bazzi_asymptotic5 b hb e x \<longleftrightarrow> 
  ln (b*x - hb*x*ln x powr -(1+e)) powr (-e/2::real) < 1"

definition "akra_bazzi_asymptotic6 b hb e x \<longleftrightarrow> hb / ln x powr (1 + e :: real) < b/2"
definition "akra_bazzi_asymptotic7 b hb e x \<longleftrightarrow> hb / ln x powr (1 + e :: real) < (1 - b) / 2"
definition "akra_bazzi_asymptotic8 b hb e x \<longleftrightarrow> x*(1 - b - hb / ln x powr (1 + e :: real)) > 1"

definition "akra_bazzi_asymptotics b hb e p x \<longleftrightarrow>
  akra_bazzi_asymptotic1 b hb e p x \<and> akra_bazzi_asymptotic1' b hb e p x \<and>
  akra_bazzi_asymptotic2 b hb e p x \<and> akra_bazzi_asymptotic2' b hb e p x \<and>
  akra_bazzi_asymptotic3 e x \<and> akra_bazzi_asymptotic4 e x \<and> akra_bazzi_asymptotic5 b hb e x \<and>
  akra_bazzi_asymptotic6 b hb e x \<and> akra_bazzi_asymptotic7 b hb e x \<and> 
  akra_bazzi_asymptotic8 b hb e x"

lemmas akra_bazzi_asymptotic_defs = 
  akra_bazzi_asymptotic1_def akra_bazzi_asymptotic1'_def 
  akra_bazzi_asymptotic2_def akra_bazzi_asymptotic2'_def akra_bazzi_asymptotic3_def
  akra_bazzi_asymptotic4_def akra_bazzi_asymptotic5_def akra_bazzi_asymptotic6_def
  akra_bazzi_asymptotic7_def akra_bazzi_asymptotic8_def akra_bazzi_asymptotics_def
  
lemma akra_bazzi_asymptotics:
  assumes "\<And>b. b \<in> set bs \<Longrightarrow> b \<in> {0<..<1}" and "e > 0"
  shows "eventually (\<lambda>x. \<forall>b\<in>set bs. akra_bazzi_asymptotics b hb e p x) at_top"
proof (intro eventually_ball_finite ballI)
  fix b assume "b \<in> set bs"
  with assms have "b \<in> {0<..<1}" by simp
  with \<open>e > 0\<close> show "eventually (\<lambda>x. akra_bazzi_asymptotics b hb e p x) at_top"
    unfolding akra_bazzi_asymptotic_defs 
    by (intro eventually_conj; real_asymp simp: mult_neg_pos)
qed simp
  
lemma
  fixes b \<epsilon> :: real
  assumes "b \<in> {0<..<1}" and "\<epsilon> > 0"
  shows "filterlim (\<lambda>x. (1 - H / (b * ln x powr (1 + \<epsilon>))) powr p * 
           (1 + ln (b * x + H * x / ln x powr (1+\<epsilon>)) powr (-\<epsilon>/2)) - 
           (1 + ln x powr (-\<epsilon>/2))) (at_right 0) at_top"
  using assms by (real_asymp simp: mult_neg_pos)

context
  fixes b e p :: real
  assumes assms: "b > 0" "e > 0"
begin

lemmas [simp] = mult_neg_pos

real_limit "(\<lambda>x. ((1 - 1 / (b * ln x powr (1 + e))) powr p * 
               (1 + ln (b * x +  x / ln x powr (1+e)) powr (-e/2)) - 
               (1 + ln x powr (-e/2))) * ln x powr ((e / 2) + 1))"
  facts: assms

end

context
  fixes b \<epsilon> :: real
  assumes assms: "b > 0" "\<epsilon> > 0" "\<epsilon> < 1 / 4"
begin

real_expansion "(\<lambda>x. (1 - H / (b * ln x powr (1 + \<epsilon>))) powr p * 
           (1 + ln (b * x + H * x / ln x powr (1+\<epsilon>)) powr (-\<epsilon>/2)) - 
           (1 + ln x powr (-\<epsilon>/2)))"
  terms: 10 (strict)
  facts: assms

end

context
  fixes e :: real
  assumes e: "e > 0" "e < 1 / 4"
begin

real_expansion "(\<lambda>x. (1 - 1 / (1/2 * ln x powr (1 + e))) * 
           (1 + ln (1/2 * x + x / ln x powr (1+e)) powr (-e/2)) - 
           (1 + ln x powr (-e/2)))"
  terms: 10 (strict)
  facts: e

end


subsection \<open>Concrete Mathematics\<close>
  
text \<open>The following inequalities are discussed on p.\ 441 in Concrete Mathematics.\<close>
lemma 
  fixes c \<epsilon> :: real
  assumes "0 < \<epsilon>" "\<epsilon> < 1" "1 < c"
    shows "(\<lambda>_::real. 1) \<in> o(\<lambda>x. ln (ln x))"
      and "(\<lambda>x::real. ln (ln x)) \<in> o(\<lambda>x. ln x)"
      and "(\<lambda>x::real. ln x) \<in> o(\<lambda>x. x powr \<epsilon>)"
      and "(\<lambda>x::real. x powr \<epsilon>) \<in> o(\<lambda>x. x powr c)"
      and "(\<lambda>x. x powr c) \<in> o(\<lambda>x. x powr ln x)"
      and "(\<lambda>x. x powr ln x) \<in> o(\<lambda>x. c powr x)"
      and "(\<lambda>x. c powr x) \<in> o(\<lambda>x. x powr x)"
      and "(\<lambda>x. x powr x) \<in> o(\<lambda>x. c powr (c powr x))"
  using assms by (real_asymp (verbose))+

    
subsection \<open>Stack Exchange\<close>

text \<open>
  http://archives.math.utk.edu/visual.calculus/1/limits.15/
\<close>
lemma "filterlim (\<lambda>x::real. (x * sin x) / abs x) (at_right 0) (at 0)"
  by real_asymp

lemma "filterlim (\<lambda>x::real. x^2 / (sqrt (x^2 + 12) - sqrt (12))) (nhds (12 / sqrt 3)) (at 0)"
proof -
  note [simp] = powr_half_sqrt sqrt_def (* TODO: Better simproc for sqrt/root? *)
  have "sqrt (12 :: real) = sqrt (4 * 3)"
    by simp
  also have "\<dots> = 2 * sqrt 3" by (subst real_sqrt_mult) simp
  finally show ?thesis by real_asymp
qed


text \<open>\<^url>\<open>http://math.stackexchange.com/questions/625574\<close>\<close>
lemma "(\<lambda>x::real. (1 - 1/2 * x^2 - cos (x / (1 - x^2))) / x^4) \<midarrow>0\<rightarrow> 23/24"
  by real_asymp


text \<open>\<^url>\<open>http://math.stackexchange.com/questions/122967\<close>\<close>

real_limit "\<lambda>x. (x + 1) powr (1 + 1 / x) - x powr (1 + 1 / (x + a))"

lemma "((\<lambda>x::real. ((x + 1) powr (1 + 1/x) - x powr (1 + 1 / (x + a)))) \<longlongrightarrow> 1) at_top"
  by real_asymp


real_limit "\<lambda>x. x ^ 2 * (arctan x - pi / 2) + x"

lemma "filterlim (\<lambda>x::real. x^2 * (arctan x - pi/2) + x) (at_right 0) at_top"
  by real_asymp


real_limit "\<lambda>x. (root 3 (x ^ 3 + x ^ 2 + x + 1) - sqrt (x ^ 2 + x + 1) * ln (exp x + x) / x)"

lemma "((\<lambda>x::real. root 3 (x^3 + x^2 + x + 1) - sqrt (x^2 + x + 1) * ln (exp x + x) / x)
           \<longlongrightarrow> -1/6) at_top"
  by real_asymp


context
  fixes a b :: real
  assumes ab: "a > 0" "b > 0"
begin
real_limit "\<lambda>x. ((a powr x - x * ln a) / (b powr x - x * ln b)) powr (1 / x ^ 2)"
  limit: "at_right 0" facts: ab
real_limit "\<lambda>x. ((a powr x - x * ln a) / (b powr x - x * ln b)) powr (1 / x ^ 2)"
  limit: "at_left 0" facts: ab
lemma "(\<lambda>x. ((a powr x - x * ln a) / (b powr x - x * ln b)) powr (1 / x ^ 2))
         \<midarrow>0\<rightarrow> exp (ln a * ln a / 2 - ln b * ln b / 2)" using ab by real_asymp
end


text \<open>\<^url>\<open>http://math.stackexchange.com/questions/547538\<close>\<close>
lemma "(\<lambda>x::real. ((x+4) powr (3/2) + exp x - 9) / x) \<midarrow>0\<rightarrow> 4"
  by real_asymp

text \<open>\<^url>\<open>https://www.freemathhelp.com/forum/threads/93513\<close>\<close>
lemma "((\<lambda>x::real. ((3 powr x + 4 powr x) / 4) powr (1/x)) \<longlongrightarrow> 4) at_top"
  by real_asymp
    
lemma "((\<lambda>x::real. x powr (3/2) * (sqrt (x + 1) + sqrt (x - 1) - 2 * sqrt x)) \<longlongrightarrow> -1/4) at_top"
  by real_asymp


text \<open>\<^url>\<open>https://www.math.ucdavis.edu/~kouba/CalcOneDIRECTORY/limcondirectory/LimitConstant.html\<close>\<close>
lemma  "(\<lambda>x::real. (cos (2*x) - 1) / (cos x - 1)) \<midarrow>0\<rightarrow> 4"
  by real_asymp

lemma "(\<lambda>x::real. tan (2*x) / (x - pi/2)) \<midarrow>pi/2\<rightarrow> 2"
  by real_asymp


text \<open>@url{"https://www.math.ucdavis.edu/~kouba/CalcOneDIRECTORY/liminfdirectory/LimitInfinity.html"}\<close>
lemma "filterlim (\<lambda>x::real. (3 powr x + 3 powr (2*x)) powr (1/x)) (nhds 9) at_top"
  using powr_def[of 3 "2::real"] by real_asymp

text \<open>\<^url>\<open>https://www.math.ucdavis.edu/~kouba/CalcOneDIRECTORY/lhopitaldirectory/LHopital.html\<close>\<close>
lemma "filterlim (\<lambda>x::real. (x^2 - 1) / (x^2 + 3*x - 4)) (nhds (2/5)) (at 1)"
  by real_asymp
    
lemma "filterlim (\<lambda>x::real. (x - 4) / (sqrt x - 2)) (nhds 4) (at 4)"
  by real_asymp
    
lemma "filterlim (\<lambda>x::real. sin x / x) (at_left 1) (at 0)"
  by real_asymp

lemma "filterlim (\<lambda>x::real. (3 powr x - 2 powr x) / (x^2 - x)) (nhds (ln (2/3))) (at 0)"
  by (real_asymp simp: ln_div)
    
lemma "filterlim (\<lambda>x::real. (1/x - 1/3) / (x^2 - 9)) (nhds (-1/54)) (at 3)"
  by real_asymp

lemma "filterlim (\<lambda>x::real. (x * tan x) / sin (3*x)) (nhds 0) (at 0)"
  by real_asymp

lemma "filterlim (\<lambda>x::real. sin (x^2) / (x * tan x)) (at 1) (at 0)"
  by real_asymp

lemma "filterlim (\<lambda>x::real. (x^2 * exp x) / tan x ^ 2) (at 1) (at 0)"
  by real_asymp

lemma "filterlim (\<lambda>x::real. exp (-1/x^2) / x^2) (at 0) (at 0)"
  by real_asymp

lemma "filterlim (\<lambda>x::real. exp x / (5 * x + 200)) at_top at_top"
  by real_asymp
    
lemma "filterlim (\<lambda>x::real. (3 + ln x) / (x^2 + 7)) (at 0) at_top"
  by real_asymp

lemma "filterlim (\<lambda>x::real. (x^2 + 3*x - 10) / (7*x^2 - 5*x + 4)) (at_right (1/7)) at_top"
  by real_asymp

lemma "filterlim (\<lambda>x::real. (ln x ^ 2) / exp (2*x)) (at_right 0) at_top"
  by real_asymp
    
lemma "filterlim (\<lambda>x::real. (3 * x + 2 powr x) / (2 * x + 3 powr x)) (at 0) at_top"
  by real_asymp
    
lemma "filterlim (\<lambda>x::real. (exp x + 2 / x) / (exp x + 5 / x)) (at_left 1) at_top"
  by real_asymp
    
lemma "filterlim (\<lambda>x::real. sqrt (x^2 + 1) - sqrt (x + 1)) at_top at_top"
  by real_asymp

  
lemma "filterlim (\<lambda>x::real. x * ln x) (at_left 0) (at_right 0)"
  by real_asymp

lemma "filterlim (\<lambda>x::real. x * ln x ^ 2) (at_right 0) (at_right 0)"
  by real_asymp

lemma "filterlim (\<lambda>x::real. ln x * tan x) (at_left 0) (at_right 0)"
  by real_asymp

lemma "filterlim (\<lambda>x::real. x powr sin x) (at_left 1) (at_right 0)"
  by real_asymp

lemma "filterlim (\<lambda>x::real. (1 + 3 / x) powr x) (at_left (exp 3)) at_top"
  by real_asymp

lemma "filterlim (\<lambda>x::real. (1 - x) powr (1 / x)) (at_left (exp (-1))) (at_right 0)"
  by real_asymp

lemma "filterlim (\<lambda>x::real. (tan x) powr x^2) (at_left 1) (at_right 0)"
  by real_asymp

lemma "filterlim (\<lambda>x::real. x powr (1 / sqrt x)) (at_right 1) at_top"
  by real_asymp

lemma "filterlim (\<lambda>x::real. ln x powr (1/x)) (at_right 1) at_top"
  by (real_asymp (verbose))

lemma "filterlim (\<lambda>x::real. x powr (x powr x)) (at_right 0) (at_right 0)"
  by (real_asymp (verbose))


text \<open>\<^url>\<open>http://calculus.nipissingu.ca/problems/limit_problems.html\<close>\<close>
lemma "((\<lambda>x::real. (x^2 - 1) / \<bar>x - 1\<bar>) \<longlongrightarrow> -2) (at_left 1)"
      "((\<lambda>x::real. (x^2 - 1) / \<bar>x - 1\<bar>) \<longlongrightarrow> 2) (at_right 1)"
  by real_asymp+

lemma "((\<lambda>x::real. (root 3 x - 1) / \<bar>sqrt x - 1\<bar>) \<longlongrightarrow> -2 / 3) (at_left 1)"
      "((\<lambda>x::real. (root 3 x - 1) / \<bar>sqrt x - 1\<bar>) \<longlongrightarrow> 2 / 3) (at_right 1)"
  by real_asymp+


text \<open>\<^url>\<open>https://math.stackexchange.com/questions/547538\<close>\<close>

lemma "(\<lambda>x::real. ((x + 4) powr (3/2) + exp x - 9) / x) \<midarrow>0\<rightarrow> 4"
  by real_asymp

text \<open>\<^url>\<open>https://math.stackexchange.com/questions/625574\<close>\<close>
lemma "(\<lambda>x::real. (1 - x^2 / 2 - cos (x / (1 - x^2))) / x^4) \<midarrow>0\<rightarrow> 23/24"
  by real_asymp

text \<open>\<^url>\<open>https://www.mapleprimes.com/questions/151308-A-Hard-Limit-Question\<close>\<close>
lemma "(\<lambda>x::real. x / (x - 1) - 1 / ln x) \<midarrow>1\<rightarrow> 1 / 2"
  by real_asymp

text \<open>\<^url>\<open>https://www.freemathhelp.com/forum/threads/93513-two-extremely-difficult-limit-problems\<close>\<close>
lemma "((\<lambda>x::real. ((3 powr x + 4 powr x) / 4) powr (1/x)) \<longlongrightarrow> 4) at_top"
  by real_asymp

lemma "((\<lambda>x::real. x powr 1.5 * (sqrt (x + 1) + sqrt (x - 1) - 2 * sqrt x)) \<longlongrightarrow> -1/4) at_top"
  by real_asymp

text \<open>\<^url>\<open>https://math.stackexchange.com/questions/1390833\<close>\<close>
context
  fixes a b :: real
  assumes ab: "a + b > 0" "a + b = 1"
begin
real_limit "\<lambda>x. (a * x powr (1 / x) + b) powr (x / ln x)"
  facts: ab
end


subsection \<open>Unsorted examples\<close>

context
  fixes a :: real
  assumes a: "a > 1"
begin

text \<open>
  It seems that Mathematica fails to expand the following example when \<open>a\<close> is a variable.
\<close>
lemma "(\<lambda>x. 1 - (1 - 1 / x powr a) powr x) \<sim> (\<lambda>x. x powr (1 - a))"
  using a by real_asymp

real_limit "\<lambda>x. (1 - (1 - 1 / x powr a) powr x) * x powr (a - 1)"
  facts: a

lemma "(\<lambda>n. log 2 (real ((n + 3) choose 3) / 4) + 1) \<sim> (\<lambda>n. 3 / ln 2 * ln n)"
proof -
  have "(\<lambda>n. log 2 (real ((n + 3) choose 3) / 4) + 1) =
          (\<lambda>n. log 2 ((real n + 1) * (real n + 2) * (real n + 3) / 24) + 1)"
    by (subst binomial_gbinomial) 
       (simp add: gbinomial_pochhammer' numeral_3_eq_3 pochhammer_Suc add_ac)
  moreover have "\<dots> \<sim> (\<lambda>n. 3 / ln 2 * ln n)"
    by (real_asymp simp: field_split_simps)
  ultimately show ?thesis by simp
qed

end

lemma "(\<lambda>x::real. exp (sin x) / ln (cos x)) \<sim>[at 0] (\<lambda>x. -2 / x ^ 2)"
  by real_asymp

real_limit "\<lambda>x. ln (1 + 1 / x) * x"
real_limit "\<lambda>x. ln x powr ln x / x"
real_limit "\<lambda>x. (arctan x - pi/2) * x"
real_limit "\<lambda>x. arctan (1/x) * x"

context
  fixes c :: real assumes c: "c \<ge> 2"
begin
lemma c': "c^2 - 3 > 0"
proof -
  from c have "c^2 \<ge> 2^2" by (rule power_mono) auto
  thus ?thesis by simp
qed

real_limit "\<lambda>x. (c^2 - 3) * exp (-x)"
real_limit "\<lambda>x. (c^2 - 3) * exp (-x)" facts: c'
end

lemma "c < 0 \<Longrightarrow> ((\<lambda>x::real. exp (c*x)) \<longlongrightarrow> 0) at_top"
  by real_asymp

lemma "filterlim (\<lambda>x::real. -exp (1/x)) (at_left 0) (at_left 0)"
  by real_asymp

lemma "((\<lambda>t::real. t^2 / (exp t - 1)) \<longlongrightarrow> 0) at_top"
  by real_asymp

lemma "(\<lambda>n. (1 + 1 / real n) ^ n) \<longlonglongrightarrow> exp 1"
  by real_asymp
  
lemma "((\<lambda>x::real. (1 + y / x) powr x) \<longlongrightarrow> exp y) at_top"
  by real_asymp

lemma "eventually (\<lambda>x::real. x < x^2) at_top"
  by real_asymp
  
lemma "eventually (\<lambda>x::real. 1 / x^2 \<ge> 1 / x) (at_left 0)"
  by real_asymp

lemma "A > 1 \<Longrightarrow> (\<lambda>n. ((1 + 1 / sqrt A) / 2) powr real_of_int (2 ^ Suc n)) \<longlonglongrightarrow> 0"
  by (real_asymp simp: field_split_simps add_pos_pos)  

lemma 
  assumes "c > (1 :: real)" "k \<noteq> 0"
  shows   "(\<lambda>n. real n ^ k) \<in> o(\<lambda>n. c ^ n)"
  using assms by (real_asymp (verbose))

lemma "(\<lambda>x::real. exp (-(x^4))) \<in> o(\<lambda>x. exp (-(x^4)) + 1 / x ^ n)"
  by real_asymp
    
lemma "(\<lambda>x::real. x^2) \<in> o[at_right 0](\<lambda>x. x)"
  by real_asymp
    
lemma "(\<lambda>x::real. x^2) \<in> o[at_left 0](\<lambda>x. x)"
  by real_asymp

lemma "(\<lambda>x::real. 2 * x + x ^ 2) \<in> \<Theta>[at_left 0](\<lambda>x. x)"
  by real_asymp
  
lemma "(\<lambda>x::real. inverse (x - 1)^2) \<in> \<omega>[at 1](\<lambda>x. x)"
  by real_asymp

lemma "(\<lambda>x::real. sin (1 / x)) \<sim> (\<lambda>x::real. 1 / x)"
  by real_asymp

lemma
  assumes "q \<in> {0<..<1}"
  shows   "LIM x at_left 1. log q (1 - x) :> at_top"
  using assms by real_asymp

context
  fixes x k :: real
  assumes xk: "x > 1" "k > 0"
begin

lemmas [simp] = add_pos_pos

real_expansion "\<lambda>l. sqrt (1 + l * (l + 1) * 4 * pi^2 * k^2 * (log x (l + 1) - log x l)^2)"
  terms: 2 facts: xk

lemma
  "(\<lambda>l. sqrt (1 + l * (l + 1) * 4 * pi^2 * k^2 * (log x (l + 1) - log x l)^2) -
          sqrt (1 + 4 * pi\<^sup>2 * k\<^sup>2 / (ln x ^ 2))) \<in> O(\<lambda>l. 1 / l ^ 2)"
  using xk by (real_asymp simp: inverse_eq_divide power_divide root_powr_inverse)

end

lemma "(\<lambda>x. (2 * x^3 - 128) / (sqrt x - 2)) \<midarrow>4\<rightarrow> 384"
  by real_asymp

lemma 
  "((\<lambda>x::real. (x^2 - 1) / abs (x - 1)) \<longlongrightarrow> 2) (at_right 1)"
  "((\<lambda>x::real. (x^2 - 1) / abs (x - 1)) \<longlongrightarrow> -2) (at_left 1)"
  by real_asymp+

lemma "(\<lambda>x::real. (root 3 x - 1) / (sqrt x - 1)) \<midarrow>1\<rightarrow> 2/3"
  by real_asymp

lemma 
  fixes a b :: real
  assumes "a > 1" "b > 1" "a \<noteq> b"
  shows   "((\<lambda>x. ((a powr x - x * ln a) / (b powr x - x * ln b)) powr (1/x^3)) \<longlongrightarrow> 1) at_top"
  using assms by real_asymp


context
  fixes a b :: real
  assumes ab: "a > 0" "b > 0"
begin

lemma 
  "((\<lambda>x. ((a powr x - x * ln a) / (b powr x - x * ln b)) powr (1 / x ^ 2)) \<longlongrightarrow>
     exp ((ln a ^ 2 - ln b ^ 2) / 2)) (at 0)"
  using ab by (real_asymp simp: power2_eq_square)

end

real_limit "\<lambda>x. 1 / sin (1/x) ^ 2 + 1 / tan (1/x) ^ 2 - 2 * x ^ 2"

real_limit "\<lambda>x. ((1 / x + 4) powr 1.5 + exp (1 / x) - 9) * x"

lemma "x > (1 :: real) \<Longrightarrow>
         ((\<lambda>n. abs (x powr n / (n * (1 + x powr (2 * n)))) powr (1 / n)) \<longlongrightarrow> 1 / x) at_top"
  by (real_asymp simp add: exp_minus field_simps)

lemma "x = (1 :: real) \<Longrightarrow>
         ((\<lambda>n. abs (x powr n / (n * (1 + x powr (2 * n)))) powr (1 / n)) \<longlongrightarrow> 1 / x) at_top"
  by (real_asymp simp add: exp_minus field_simps)

lemma "x > (0 :: real) \<Longrightarrow> x < 1 \<Longrightarrow>
         ((\<lambda>n. abs (x powr n / (n * (1 + x powr (2 * n)))) powr (1 / n)) \<longlongrightarrow> x) at_top"
  by real_asymp

lemma "(\<lambda>x. (exp (sin b) - exp (sin (b * x))) * tan (pi * x / 2)) \<midarrow>1\<rightarrow>
         (2*b/pi * exp (sin b) * cos b)"
  by real_asymp

(* SLOW *)
lemma "filterlim (\<lambda>x::real. (sin (tan x) - tan (sin x))) (at 0) (at 0)"
  by real_asymp

(* SLOW *)
lemma "(\<lambda>x::real. 1 / sin x powr (tan x ^ 2)) \<midarrow>pi/2\<rightarrow> exp (1 / 2)"
  by (real_asymp simp: exp_minus)

lemma "a > 0 \<Longrightarrow> b > 0 \<Longrightarrow> c > 0 \<Longrightarrow>
  filterlim (\<lambda>x::real. ((a powr x + b powr x + c powr x) / 3) powr (3 / x))
    (nhds (a * b * c)) (at 0)"
  by (real_asymp simp: exp_add add_divide_distrib exp_minus algebra_simps)

real_expansion "\<lambda>x. arctan (sin (1 / x))"

real_expansion "\<lambda>x. ln (1 + 1 / x)"
  terms: 5 (strict)

real_expansion "\<lambda>x. sqrt (x + 1) - sqrt (x - 1)"
  terms: 3 (strict)


text \<open>
  In this example, the first 7 terms of \<open>tan (sin x)\<close> and \<open>sin (tan x)\<close> coincide, which makes
  the calculation a bit slow.
\<close>
real_limit "\<lambda>x. (tan (sin x) - sin (tan x)) / x ^ 7" limit: "at_right 0"

(* SLOW *)
real_expansion "\<lambda>x. sin (tan (1/x)) - tan (sin (1/x))"
  terms: 1 (strict)

(* SLOW *)
real_expansion "\<lambda>x. tan (1 / x)"
  terms: 6

real_expansion "\<lambda>x::real. arctan x"

real_expansion "\<lambda>x. sin (tan (1/x))"

real_expansion "\<lambda>x. (sin (-1 / x) ^ 2) powr sin (-1/x)"

real_limit "\<lambda>x. exp (max (sin x) 1)"

lemma "filterlim (\<lambda>x::real. 1 - 1 / x + ln x) at_top at_top"
  by (force intro: tendsto_diff filterlim_tendsto_add_at_top
        real_tendsto_divide_at_top filterlim_ident ln_at_top)

lemma "filterlim (\<lambda>i::real. i powr (-i/(i-1)) - i powr (-1/(i-1))) (at_left 1) (at_right 0)"
  by real_asymp

lemma "filterlim (\<lambda>i::real. i powr (-i/(i-1)) - i powr (-1/(i-1))) (at_right (-1)) at_top"
  by real_asymp

lemma "eventually (\<lambda>i::real. i powr (-i/(i-1)) - i powr (-1/(i-1)) < 1) (at_right 0)"
  and "eventually (\<lambda>i::real. i powr (-i/(i-1)) - i powr (-1/(i-1)) > -1) at_top"
  by real_asymp+

end


subsection \<open>Interval arithmetic tests\<close>

lemma "filterlim (\<lambda>x::real. x + sin x) at_top at_top"
      "filterlim (\<lambda>x::real. sin x + x) at_top at_top"
      "filterlim (\<lambda>x::real. x + (sin x + sin x)) at_top at_top"
  by real_asymp+

lemma "filterlim (\<lambda>x::real. 2 * x + sin x * x) at_infinity at_top"
      "filterlim (\<lambda>x::real. 2 * x + (sin x + 1) * x) at_infinity at_top"
      "filterlim (\<lambda>x::real. 3 * x + (sin x - 1) * x) at_infinity at_top"
      "filterlim (\<lambda>x::real. 2 * x + x * sin x) at_infinity at_top"
      "filterlim (\<lambda>x::real. 2 * x + x * (sin x + 1)) at_infinity at_top"
      "filterlim (\<lambda>x::real. 3 * x + x * (sin x - 1)) at_infinity at_top"

      "filterlim (\<lambda>x::real. x + sin x * sin x) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + sin x * (sin x + 1)) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + sin x * (sin x - 1)) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + sin x * (sin x + 2)) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + sin x * (sin x - 2)) at_infinity at_top"

      "filterlim (\<lambda>x::real. x + (sin x - 1) * sin x) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + (sin x - 1) * (sin x + 1)) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + (sin x - 1) * (sin x - 1)) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + (sin x - 1) * (sin x + 2)) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + (sin x - 1) * (sin x - 2)) at_infinity at_top"

      "filterlim (\<lambda>x::real. x + (sin x - 2) * sin x) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + (sin x - 2) * (sin x + 1)) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + (sin x - 2) * (sin x - 1)) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + (sin x - 2) * (sin x + 2)) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + (sin x - 2) * (sin x - 2)) at_infinity at_top"

      "filterlim (\<lambda>x::real. x + (sin x + 1) * sin x) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + (sin x + 1) * (sin x + 1)) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + (sin x + 1) * (sin x - 1)) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + (sin x + 1) * (sin x + 2)) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + (sin x + 1) * (sin x - 2)) at_infinity at_top"

      "filterlim (\<lambda>x::real. x + (sin x + 2) * sin x) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + (sin x + 2) * (sin x + 1)) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + (sin x + 2) * (sin x - 1)) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + (sin x + 2) * (sin x + 2)) at_infinity at_top"
      "filterlim (\<lambda>x::real. x + (sin x + 2) * (sin x - 2)) at_infinity at_top"
  by real_asymp+

lemma "filterlim (\<lambda>x::real. x * inverse (sin x + 2)) at_top at_top"
      "filterlim (\<lambda>x::real. x * inverse (sin x - 2)) at_bot at_top"
      "filterlim (\<lambda>x::real. x / inverse (sin x + 2)) at_top at_top"
      "filterlim (\<lambda>x::real. x / inverse (sin x - 2)) at_bot at_top"
  by real_asymp+

lemma "filterlim (\<lambda>x::real. \<lfloor>x\<rfloor>) at_top at_top"
      "filterlim (\<lambda>x::real. \<lceil>x\<rceil>) at_top at_top"
      "filterlim (\<lambda>x::real. nat \<lfloor>x\<rfloor>) at_top at_top"
      "filterlim (\<lambda>x::real. nat \<lceil>x\<rceil>) at_top at_top"
      "filterlim (\<lambda>x::int. nat x) at_top at_top"
      "filterlim (\<lambda>x::int. nat x) at_top at_top"
      "filterlim (\<lambda>n::nat. real (n mod 42) + real n) at_top at_top"
  by real_asymp+

lemma "(\<lambda>n. real_of_int \<lfloor>n\<rfloor>) \<sim>[at_top] (\<lambda>n. real_of_int n)"
      "(\<lambda>n. sqrt \<lfloor>n\<rfloor>) \<sim>[at_top] (\<lambda>n. sqrt n)"
  by real_asymp+

lemma
  "c > 1 \<Longrightarrow> (\<lambda>n::nat. 2 ^ (n div c) :: int) \<in> o(\<lambda>n. 2 ^ n)"
  by (real_asymp simp: field_simps)

lemma
  "c > 1 \<Longrightarrow> (\<lambda>n::nat. 2 ^ (n div c) :: nat) \<in> o(\<lambda>n. 2 ^ n)"
  by (real_asymp simp: field_simps)

end