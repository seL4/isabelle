(*  Title:      HOL/Computational_Algebra/Computation_Checks.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Computation checks\<close>

theory Computation_Checks
imports Primes Polynomial_Factorial
begin

text \<open>
  @{lemma \<open>prime (997::nat)\<close> by eval}
\<close>

text \<open>
  @{lemma \<open>prime (997::int)\<close> by eval}
\<close>

text \<open>
  @{lemma \<open>Gcd {[:1, 2, 3:], [:2, 3, (4 :: int):]} = 1\<close> by eval}
\<close>

text \<open>
  @{lemma \<open>Lcm {[:1, 2, 3:], [:2, 3, 4:]} = [:[:2:], [:7:], [:16:], [:17:], [:12 :: int:]:]\<close> by eval}
\<close>

end

