theory Approximation_Quickcheck_Ex
imports "../Approximation"
begin

lemma
  fixes x::real and y::real
  shows "sin x \<le> tan x"
  using [[quickcheck_approximation_custom_seed = 1]]
  quickcheck[approximation, expect=counterexample]
  oops

lemma "x \<le> y \<Longrightarrow> arctan y / y \<le> arctan x / x"
  using [[quickcheck_approximation_custom_seed = 1]]
  quickcheck[approximation, expect=counterexample]
  oops

lemma "0 < x \<Longrightarrow> x \<le> y \<Longrightarrow> arctan y / y \<le> arctan x / x"
  using [[quickcheck_approximation_custom_seed = 1]]
  quickcheck[approximation, expect=no_counterexample]
  by (rule arctan_divide_mono)

lemma
  fixes x::real
  shows "exp (exp x + exp y + sin x * sin y) - 0.4 > 0 \<or> 0.98 - sin x / (sin x * sin y + 2)^2 > 0"
  using [[quickcheck_approximation_custom_seed = 1]]
  quickcheck[approximation, expect=counterexample, size=10, iterations=1000, verbose]
  oops

lemma
  fixes x::real
  shows "x > 1 \<Longrightarrow> x \<le> 2 powr 20 * log 2 x + 1 \<and> (sin x)\<^sup>2 + (cos x)\<^sup>2 = 1"
  using [[quickcheck_approximation_custom_seed = 1]]
  using [[quickcheck_approximation_epsilon = 0.00000001]]
    --\<open>avoids spurious counterexamples in approximate computation of @{term "(sin x)\<^sup>2 + (cos x)\<^sup>2"}
      and therefore avoids expensive failing attempts for certification\<close>
  quickcheck[approximation, expect=counterexample, size=20]
  oops

end
