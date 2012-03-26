(*  Title:  HOL/ex/Arith_Examples.thy
    Author: Tjark Weber
*)

header {* Arithmetic *}

theory Arith_Examples
imports Main
begin

text {*
  The @{text arith} method is used frequently throughout the Isabelle
  distribution.  This file merely contains some additional tests and special
  corner cases.  Some rather technical remarks:

  @{ML Lin_Arith.simple_tac} is a very basic version of the tactic.  It performs no
  meta-to-object-logic conversion, and only some splitting of operators.
  @{ML Lin_Arith.tac} performs meta-to-object-logic conversion, full
  splitting of operators, and NNF normalization of the goal.  The @{text arith}
  method combines them both, and tries other methods (e.g.~@{text presburger})
  as well.  This is the one that you should use in your proofs!

  An @{text arith}-based simproc is available as well (see @{ML
  Lin_Arith.simproc}), which---for performance
  reasons---however does even less splitting than @{ML Lin_Arith.simple_tac}
  at the moment (namely inequalities only).  (On the other hand, it
  does take apart conjunctions, which @{ML Lin_Arith.simple_tac} currently
  does not do.)
*}


subsection {* Splitting of Operators: @{term max}, @{term min}, @{term abs},
           @{term minus}, @{term nat}, @{term Divides.mod},
           @{term Divides.div} *}

lemma "(i::nat) <= max i j"
  by linarith

lemma "(i::int) <= max i j"
  by linarith

lemma "min i j <= (i::nat)"
  by linarith

lemma "min i j <= (i::int)"
  by linarith

lemma "min (i::nat) j <= max i j"
  by linarith

lemma "min (i::int) j <= max i j"
  by linarith

lemma "min (i::nat) j + max i j = i + j"
  by linarith

lemma "min (i::int) j + max i j = i + j"
  by linarith

lemma "(i::nat) < j ==> min i j < max i j"
  by linarith

lemma "(i::int) < j ==> min i j < max i j"
  by linarith

lemma "(0::int) <= abs i"
  by linarith

lemma "(i::int) <= abs i"
  by linarith

lemma "abs (abs (i::int)) = abs i"
  by linarith

text {* Also testing subgoals with bound variables. *}

lemma "!!x. (x::nat) <= y ==> x - y = 0"
  by linarith

lemma "!!x. (x::nat) - y = 0 ==> x <= y"
  by linarith

lemma "!!x. ((x::nat) <= y) = (x - y = 0)"
  by linarith

lemma "[| (x::nat) < y; d < 1 |] ==> x - y = d"
  by linarith

lemma "[| (x::nat) < y; d < 1 |] ==> x - y - x = d - x"
  by linarith

lemma "(x::int) < y ==> x - y < 0"
  by linarith

lemma "nat (i + j) <= nat i + nat j"
  by linarith

lemma "i < j ==> nat (i - j) = 0"
  by linarith

lemma "(i::nat) mod 0 = i"
  (* rule split_mod is only declared by default for numerals *)
  using split_mod [of _ _ "0", arith_split]
  by linarith

lemma "(i::nat) mod 1 = 0"
  (* rule split_mod is only declared by default for numerals *)
  using split_mod [of _ _ "1", arith_split]
  by linarith

lemma "(i::nat) mod 42 <= 41"
  by linarith

lemma "(i::int) mod 0 = i"
  (* rule split_zmod is only declared by default for numerals *)
  using split_zmod [of _ _ "0", arith_split]
  by linarith

lemma "(i::int) mod 1 = 0"
  (* rule split_zmod is only declared by default for numerals *)
  using split_zmod [of _ _ "1", arith_split]
  by linarith

lemma "(i::int) mod 42 <= 41"
  by linarith

lemma "-(i::int) * 1 = 0 ==> i = 0"
  by linarith

lemma "[| (0::int) < abs i; abs i * 1 < abs i * j |] ==> 1 < abs i * j"
  by linarith


subsection {* Meta-Logic *}

lemma "x < Suc y == x <= y"
  by linarith

lemma "((x::nat) == z ==> x ~= y) ==> x ~= y | z ~= y"
  by linarith


subsection {* Various Other Examples *}

lemma "(x < Suc y) = (x <= y)"
  by linarith

lemma "[| (x::nat) < y; y < z |] ==> x < z"
  by linarith

lemma "(x::nat) < y & y < z ==> x < z"
  by linarith

text {* This example involves no arithmetic at all, but is solved by
  preprocessing (i.e. NNF normalization) alone. *}

lemma "(P::bool) = Q ==> Q = P"
  by linarith

lemma "[| P = (x = 0); (~P) = (y = 0) |] ==> min (x::nat) y = 0"
  by linarith

lemma "[| P = (x = 0); (~P) = (y = 0) |] ==> max (x::nat) y = x + y"
  by linarith

lemma "[| (x::nat) ~= y; a + 2 = b; a < y; y < b; a < x; x < b |] ==> False"
  by linarith

lemma "[| (x::nat) > y; y > z; z > x |] ==> False"
  by linarith

lemma "(x::nat) - 5 > y ==> y < x"
  by linarith

lemma "(x::nat) ~= 0 ==> 0 < x"
  by linarith

lemma "[| (x::nat) ~= y; x <= y |] ==> x < y"
  by linarith

lemma "[| (x::nat) < y; P (x - y) |] ==> P 0"
  by linarith

lemma "(x - y) - (x::nat) = (x - x) - y"
  by linarith

lemma "[| (a::nat) < b; c < d |] ==> (a - b) = (c - d)"
  by linarith

lemma "((a::nat) - (b - (c - (d - e)))) = (a - (b - (c - (d - e))))"
  by linarith

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
(* by (tactic {* Lin_Arith.tac 1 *}) *)
oops

lemma "2 * (x::nat) ~= 1"
(* FIXME: this is beyond the scope of the decision procedure at the moment, *)
(*        because its negation is satisfiable in the rationals?             *)
(* by (tactic {* Lin_Arith.simple_tac 1 *}) *)
oops

text {* Constants. *}

lemma "(0::nat) < 1"
  by linarith

lemma "(0::int) < 1"
  by linarith

lemma "(47::nat) + 11 < 8 * 15"
  by linarith

lemma "(47::int) + 11 < 8 * 15"
  by linarith

text {* Splitting of inequalities of different type. *}

lemma "[| (a::nat) ~= b; (i::int) ~= j; a < 2; b < 2 |] ==>
  a + b <= nat (max (abs i) (abs j))"
  by linarith

text {* Again, but different order. *}

lemma "[| (i::int) ~= j; (a::nat) ~= b; a < 2; b < 2 |] ==>
  a + b <= nat (max (abs i) (abs j))"
  by linarith

end
