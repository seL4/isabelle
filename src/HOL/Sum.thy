(*  Title:      HOL/Sum.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

The disjoint sum of two types.
*)

Sum = mono + Prod +

(* type definition *)

constdefs
  Inl_Rep       :: ['a, 'a, 'b, bool] => bool
  "Inl_Rep == (%a. %x y p. x=a & p)"

  Inr_Rep       :: ['b, 'a, 'b, bool] => bool
  "Inr_Rep == (%b. %x y p. y=b & ~p)"

global

typedef (Sum)
  ('a, 'b) "+"          (infixr 10)
    = "{f. (? a. f = Inl_Rep(a::'a)) | (? b. f = Inr_Rep(b::'b))}"


(* abstract constants and syntax *)

consts
  Inl            :: "'a => 'a + 'b"
  Inr            :: "'b => 'a + 'b"

  (*disjoint sum for sets; the operator + is overloaded with wrong type!*)
  Plus          :: "['a set, 'b set] => ('a + 'b) set"        (infixr 65)
  Part          :: ['a set, 'b => 'a] => 'a set

local

defs
  Inl_def       "Inl == (%a. Abs_Sum(Inl_Rep(a)))"
  Inr_def       "Inr == (%b. Abs_Sum(Inr_Rep(b)))"

  sum_def       "A Plus B == (Inl``A) Un (Inr``B)"

  (*for selecting out the components of a mutually recursive definition*)
  Part_def      "Part A h == A Int {x. ? z. x = h(z)}"

end
