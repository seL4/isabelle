(*  Title:  HOL/ex/Arith_Examples.thy
    ID:     $Id$
    Author: Tjark Weber
*)

header {* {\tt arith} *}

theory Arith_Examples imports Main begin

text {*
  The {\tt arith} tactic is used frequently throughout the Isabelle
  distribution.  This file merely contains some additional tests and special
  corner cases.  Some rather technical remarks:

  {\tt fast_arith_tac} is a very basic version of the tactic.  It performs no
  meta-to-object-logic conversion, and only some splitting of operators.
  {\tt simple_arith_tac} performs meta-to-object-logic conversion, full
  splitting of operators, and NNF normalization of the goal.  The {\tt arith}
  tactic combines them both, and tries other tactics (e.g.~{\tt presburger})
  as well.  This is the one that you should use in your proofs!

  An {\tt arith}-based simproc is available as well (see {\tt
  Fast_Arith.lin_arith_prover}), which---for performance reasons---however
  does even less splitting than {\tt fast_arith_tac} at the moment (namely
  inequalities only).  (On the other hand, it does take apart conjunctions,
  which {\tt fast_arith_tac} currently does not do.)
*}

ML {* set trace_arith; *}

section {* Splitting of Operators: @{term max}, @{term min}, @{term abs},
           @{term HOL.minus}, @{term nat}, @{term Divides.mod},
           @{term Divides.div} *}

lemma "(i::nat) <= max i j"
  by (tactic {* fast_arith_tac 1 *})

lemma "(i::int) <= max i j"
  by (tactic {* fast_arith_tac 1 *})

lemma "min i j <= (i::nat)"
  by (tactic {* fast_arith_tac 1 *})

lemma "min i j <= (i::int)"
  by (tactic {* fast_arith_tac 1 *})

lemma "min (i::nat) j <= max i j"
  by (tactic {* fast_arith_tac 1 *})

lemma "min (i::int) j <= max i j"
  by (tactic {* fast_arith_tac 1 *})

lemma "(i::nat) < j ==> min i j < max i j"
  by (tactic {* fast_arith_tac 1 *})

lemma "(i::int) < j ==> min i j < max i j"
  by (tactic {* fast_arith_tac 1 *})

lemma "(0::int) <= abs i"
  by (tactic {* fast_arith_tac 1 *})

lemma "(i::int) <= abs i"
  by (tactic {* fast_arith_tac 1 *})

lemma "abs (abs (i::int)) = abs i"
  by (tactic {* fast_arith_tac 1 *})

text {* Also testing subgoals with bound variables. *}

lemma "!!x. (x::nat) <= y ==> x - y = 0"
  by (tactic {* fast_arith_tac 1 *})

lemma "!!x. (x::nat) - y = 0 ==> x <= y"
  by (tactic {* fast_arith_tac 1 *})

lemma "!!x. ((x::nat) <= y) = (x - y = 0)"
  by (tactic {* simple_arith_tac 1 *})

lemma "[| (x::nat) < y; d < 1 |] ==> x - y = d"
  by (tactic {* fast_arith_tac 1 *})

lemma "[| (x::nat) < y; d < 1 |] ==> x - y - x = d - x"
  by (tactic {* fast_arith_tac 1 *})

lemma "(x::int) < y ==> x - y < 0"
  by (tactic {* fast_arith_tac 1 *})

lemma "nat (i + j) <= nat i + nat j"
  by (tactic {* fast_arith_tac 1 *})

lemma "i < j ==> nat (i - j) = 0"
  by (tactic {* fast_arith_tac 1 *})

lemma "(i::nat) mod 0 = i"
oops

lemma "(i::nat) mod (Suc 0) = 0"
oops

lemma "(i::nat) div 0 = 0"
oops

ML {* (#splits (ArithTheoryData.get (the_context ()))); *}

lemma "(i::nat) mod (number_of (1::int)) = 0"
oops

section {* Meta-Logic *}

lemma "x < Suc y == x <= y"
  by (tactic {* simple_arith_tac 1 *})

lemma "((x::nat) == z ==> x ~= y) ==> x ~= y | z ~= y"
  by (tactic {* simple_arith_tac 1 *})

section {* Other Examples *}

lemma "[| (x::nat) < y; y < z |] ==> x < z"
  by (tactic {* fast_arith_tac 1 *})

lemma "(x::nat) < y & y < z ==> x < z"
  by (tactic {* simple_arith_tac 1 *})

lemma "[| (x::nat) ~= y; a + 2 = b; a < y; y < b; a < x; x < b |] ==> False"
  by (tactic {* fast_arith_tac 1 *})

lemma "[| (x::nat) > y; y > z; z > x |] ==> False"
  by (tactic {* fast_arith_tac 1 *})

lemma "(x::nat) - 5 > y ==> y < x"
  by (tactic {* fast_arith_tac 1 *})

lemma "(x::nat) ~= 0 ==> 0 < x"
  by (tactic {* fast_arith_tac 1 *})

lemma "[| (x::nat) ~= y; x <= y |] ==> x < y"
  by (tactic {* fast_arith_tac 1 *})

lemma "(x::nat) < y \<longrightarrow> P (x - y) \<longrightarrow> P 0"
  by (tactic {* simple_arith_tac 1 *})

lemma "(x - y) - (x::nat) = (x - x) - y"
  by (tactic {* fast_arith_tac 1 *})

lemma "[| (a::nat) < b; c < d |] ==> (a - b) = (c - d)"
  by (tactic {* fast_arith_tac 1 *})

lemma "((a::nat) - (b - (c - (d - e)))) = (a - (b - (c - (d - e))))"
  by (tactic {* fast_arith_tac 1 *})

text {* Splitting of inequalities of different type. *}

lemma "[| (a::nat) ~= b; (i::int) ~= j; a < 2; b < 2 |] ==>
  a + b <= nat (max (abs i) (abs j))"
  by (tactic {* fast_arith_tac 1 *})

lemma "[| (i::int) ~= j; (a::nat) ~= b; a < 2; b < 2 |] ==>
  a + b <= nat (max (abs i) (abs j))"
  by (tactic {* fast_arith_tac 1 *})

ML {* reset trace_arith; *}

end
