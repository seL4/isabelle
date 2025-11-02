(*  Title:      HOL/Computational_Algebra/Computation_Checks.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Computation checks\<close>

theory Computation_Checks
imports Primes Polynomial_Factorial "HOL-Library.Discrete_Functions" "HOL-Library.Code_Target_Numeral"
begin

text \<open>
  @{lemma \<open>floor_sqrt 16476148165462159 = 128359449\<close> by eval}
\<close>

text \<open>
  @{lemma \<open>prime (97 :: nat)\<close> by simp}
\<close>

text \<open>
  @{lemma \<open>prime (97 :: int)\<close> by simp}
\<close>

text \<open>
  @{lemma \<open>prime (9973 :: nat)\<close> by eval}
\<close>

text \<open>
  @{lemma \<open>prime (9973 :: int)\<close> by eval}
\<close>

text \<open>
  @{lemma \<open>Gcd {[:1, 2, 3:], [:2, 3, (4 :: int):]} = 1\<close> by eval}
\<close>

text \<open>
  @{lemma \<open>Lcm {[:1, 2, 3:], [:2, 3, 4:]} = [:[:2:], [:7:], [:16:], [:17:], [:12 :: int:]:]\<close> by eval}
\<close>

end

