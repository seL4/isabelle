(*  Title:      HOL/ex/Comb.thy
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1996  University of Cambridge

Combinatory Logic example: the Church-Rosser Theorem
Curiously, combinators do not include free variables.

Example taken from
    J. Camilleri and T. F. Melham.
    Reasoning with Inductively Defined Relations in the HOL Theorem Prover.
    Report 265, University of Cambridge Computer Laboratory, 1992.
*)


Comb = Trancl +

(** Datatype definition of combinators S and K, with infixed application **)
datatype comb = K
              | S
              | "#" comb comb (infixl 90)

(** Inductive definition of contractions, -1->
             and (multi-step) reductions, --->
**)
consts
  contract  :: "(comb*comb) set"
  "-1->"    :: [comb,comb] => bool   (infixl 50)
  "--->"    :: [comb,comb] => bool   (infixl 50)

translations
  "x -1-> y" == "(x,y) : contract"
  "x ---> y" == "(x,y) : contract^*"

inductive contract
  intrs
    K     "K#x#y -1-> x"
    S     "S#x#y#z -1-> (x#z)#(y#z)"
    Ap1   "x-1->y ==> x#z -1-> y#z"
    Ap2   "x-1->y ==> z#x -1-> z#y"


(** Inductive definition of parallel contractions, =1=>
             and (multi-step) parallel reductions, ===>
**)
consts
  parcontract :: "(comb*comb) set"
  "=1=>"    :: [comb,comb] => bool   (infixl 50)
  "===>"    :: [comb,comb] => bool   (infixl 50)

translations
  "x =1=> y" == "(x,y) : parcontract"
  "x ===> y" == "(x,y) : parcontract^*"

inductive parcontract
  intrs
    refl  "x =1=> x"
    K     "K#x#y =1=> x"
    S     "S#x#y#z =1=> (x#z)#(y#z)"
    Ap    "[| x=1=>y;  z=1=>w |] ==> x#z =1=> y#w"


(*Misc definitions*)
constdefs
  I :: comb
  "I == S#K#K"

  (*confluence; Lambda/Commutation treats this more abstractly*)
  diamond   :: "('a * 'a)set => bool"	
  "diamond(r) == ALL x y. (x,y):r --> 
                  (ALL y'. (x,y'):r --> 
                    (EX z. (y,z):r & (y',z) : r))"

end
