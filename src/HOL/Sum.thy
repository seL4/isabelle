(*  Title:      HOL/Sum.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

The disjoint sum of two types.
*)

Sum = mono + Prod +

(* type definition *)

consts
  Inl_Rep       :: ['a, 'a, 'b, bool] => bool
  Inr_Rep       :: ['b, 'a, 'b, bool] => bool

defs
  Inl_Rep_def   "Inl_Rep == (%a. %x y p. x=a & p)"
  Inr_Rep_def   "Inr_Rep == (%b. %x y p. y=b & ~p)"

typedef (Sum)
  ('a, 'b) "+"          (infixr 10)
    = "{f. (? a. f = Inl_Rep(a::'a)) | (? b. f = Inr_Rep(b::'b))}"


(* abstract constants and syntax *)

consts
  Inl           :: "'a => 'a + 'b"
  Inr           :: "'b => 'a + 'b"
  sum_case      :: "['a => 'c, 'b => 'c, 'a + 'b] => 'c"

  (*disjoint sum for sets; the operator + is overloaded with wrong type!*)
  "plus"        :: "['a set, 'b set] => ('a + 'b) set"        (infixr 65)
  Part          :: ['a set, 'b => 'a] => 'a set

translations
  "case p of Inl(x) => a | Inr(y) => b" == "sum_case (%x.a) (%y.b) p"

defs
  Inl_def       "Inl == (%a. Abs_Sum(Inl_Rep(a)))"
  Inr_def       "Inr == (%b. Abs_Sum(Inr_Rep(b)))"
  sum_case_def  "sum_case f g p == @z.  (!x. p=Inl(x) --> z=f(x))      
                                      & (!y. p=Inr(y) --> z=g(y))"

  sum_def       "A plus B == (Inl``A) Un (Inr``B)"

  (*for selecting out the components of a mutually recursive definition*)
  Part_def      "Part A h == A Int {x. ? z. x = h(z)}"

end
