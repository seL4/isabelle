(*  Title:      ZF/UNITY/Monotonicity.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge

Monotonicity of an operator (meta-function) with respect to arbitrary set relations.
*)

Monotonicity =  GenPrefix  +  MultisetSum +
constdefs
mono1 :: [i, i, i, i, i=>i] => o
"mono1(A, r, B, s, f) ==
 (ALL x:A. ALL y:A. <x, y>:r --> <f(x), f(y)>:s) & (ALL x:A. f(x):B)"

  (* monotonicity of a 2-place meta-function f *)

  mono2 :: [i, i, i, i, i, i, [i,i]=>i] => o
  "mono2(A, r, B, s, C, t, f) == (ALL x:A. ALL y:A. ALL u:B. ALL v:B.
    <x, y>:r & <u,v>:s --> <f(x, u), f(y,v)>:t) &
    (ALL x:A. ALL y:B. f(x,y):C)"

 (* Internalized relations on sets and multisets *)

  SetLe :: i =>i
  "SetLe(A) == {<x, y>:Pow(A)*Pow(A). x <= y}"

  MultLe :: [i,i] =>i
  "MultLe(A, r) == multirel(A, r - id(A)) Un id(Mult(A))"

end