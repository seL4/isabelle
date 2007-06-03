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

  \verb!fast_arith_tac! is a very basic version of the tactic.  It performs no
  meta-to-object-logic conversion, and only some splitting of operators.
  \verb!simple_arith_tac! performs meta-to-object-logic conversion, full
  splitting of operators, and NNF normalization of the goal.  The {\tt arith}
  tactic combines them both, and tries other tactics (e.g.~{\tt presburger})
  as well.  This is the one that you should use in your proofs!

  An {\tt arith}-based simproc is available as well
  (see \verb!Fast_Arith.lin_arith_prover!),
  which---for performance reasons---however
  does even less splitting than \verb!fast_arith_tac! at the moment (namely
  inequalities only).  (On the other hand, it does take apart conjunctions,
  which \verb!fast_arith_tac! currently does not do.)
*}

(*
ML {* set trace_arith; *}
*)

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

lemma "min (i::nat) j + max i j = i + j"
  by (tactic {* fast_arith_tac 1 *})

lemma "min (i::int) j + max i j = i + j"
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
  (* FIXME: need to replace 0 by its numeral representation *)
  apply (subst nat_numeral_0_eq_0 [symmetric])
  by (tactic {* fast_arith_tac 1 *})

lemma "(i::nat) mod 1 = 0"
  (* FIXME: need to replace 1 by its numeral representation *)
  apply (subst nat_numeral_1_eq_1 [symmetric])
  by (tactic {* fast_arith_tac 1 *})

lemma "(i::nat) mod 42 <= 41"
  by (tactic {* fast_arith_tac 1 *})

lemma "(i::int) mod 0 = i"
  (* FIXME: need to replace 0 by its numeral representation *)
  apply (subst numeral_0_eq_0 [symmetric])
  by (tactic {* fast_arith_tac 1 *})

lemma "(i::int) mod 1 = 0"
  (* FIXME: need to replace 1 by its numeral representation *)
  apply (subst numeral_1_eq_1 [symmetric])
  (* FIXME: arith does not know about iszero *)
  apply (tactic {* LA_Data_Ref.pre_tac 1 *})
oops

lemma "(i::int) mod 42 <= 41"
  (* FIXME: arith does not know about iszero *)
  apply (tactic {* LA_Data_Ref.pre_tac 1 *})
oops

section {* Meta-Logic *}

lemma "x < Suc y == x <= y"
  by (tactic {* simple_arith_tac 1 *})

lemma "((x::nat) == z ==> x ~= y) ==> x ~= y | z ~= y"
  by (tactic {* simple_arith_tac 1 *})

section {* Various Other Examples *}

lemma "(x < Suc y) = (x <= y)"
  by (tactic {* simple_arith_tac 1 *})

lemma "[| (x::nat) < y; y < z |] ==> x < z"
  by (tactic {* fast_arith_tac 1 *})

lemma "(x::nat) < y & y < z ==> x < z"
  by (tactic {* simple_arith_tac 1 *})

text {* This example involves no arithmetic at all, but is solved by
  preprocessing (i.e. NNF normalization) alone. *}

lemma "(P::bool) = Q ==> Q = P"
  by (tactic {* simple_arith_tac 1 *})

lemma "[| P = (x = 0); (~P) = (y = 0) |] ==> min (x::nat) y = 0"
  by (tactic {* simple_arith_tac 1 *})

lemma "[| P = (x = 0); (~P) = (y = 0) |] ==> max (x::nat) y = x + y"
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

lemma "[| (x::nat) < y; P (x - y) |] ==> P 0"
  by (tactic {* simple_arith_tac 1 *})

lemma "(x - y) - (x::nat) = (x - x) - y"
  by (tactic {* fast_arith_tac 1 *})

lemma "[| (a::nat) < b; c < d |] ==> (a - b) = (c - d)"
  by (tactic {* fast_arith_tac 1 *})

lemma "((a::nat) - (b - (c - (d - e)))) = (a - (b - (c - (d - e))))"
  by (tactic {* fast_arith_tac 1 *})

lemma "(n < m & m < n') | (n < m & m = n') | (n < n' & n' < m) |
  (n = n' & n' < m) | (n = m & m < n') |
  (n' < m & m < n) | (n' < m & m = n) |
  (n' < n & n < m) | (n' = n & n < m) | (n' = m & m < n) |
  (m < n & n < n') | (m < n & n' = n) | (m < n' & n' < n) |
  (m = n & n < n') | (m = n' & n' < n) |
  (n' = m & m = (n::nat))"
(* FIXME: this should work in principle, but is extremely slow because     *)
(*        preprocessing negates the goal and tries to compute its negation *)
(*        normal form, which creates lots of separate cases for this       *)
(*        disjunction of conjunctions                                      *)
(* by (tactic {* simple_arith_tac 1 *}) *)
oops

lemma "2 * (x::nat) ~= 1"
(* FIXME: this is beyond the scope of the decision procedure at the moment, *)
(*        because its negation is satisfiable in the rationals?             *)
(* by (tactic {* fast_arith_tac 1 *}) *)
oops

text {* Constants. *}

lemma "(0::nat) < 1"
  by (tactic {* fast_arith_tac 1 *})

lemma "(0::int) < 1"
  by (tactic {* fast_arith_tac 1 *})

lemma "(47::nat) + 11 < 08 * 15"
  by (tactic {* fast_arith_tac 1 *})

lemma "(47::int) + 11 < 08 * 15"
  by (tactic {* fast_arith_tac 1 *})

text {* Splitting of inequalities of different type. *}

lemma "[| (a::nat) ~= b; (i::int) ~= j; a < 2; b < 2 |] ==>
  a + b <= nat (max (abs i) (abs j))"
  by (tactic {* fast_arith_tac 1 *})

text {* Again, but different order. *}

lemma "[| (i::int) ~= j; (a::nat) ~= b; a < 2; b < 2 |] ==>
  a + b <= nat (max (abs i) (abs j))"
  by (tactic {* fast_arith_tac 1 *})

(*
ML {* reset trace_arith; *}
*)

end
