(*  Title:      ZF/ex/Comb.thy
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1994  University of Cambridge

Combinatory Logic example: the Church-Rosser Theorem
Curiously, combinators do not include free variables.

Example taken from
    J. Camilleri and T. F. Melham.
    Reasoning with Inductively Defined Relations in the HOL Theorem Prover.
    Report 265, University of Cambridge Computer Laboratory, 1992.
*)


Comb = Datatype +

(** Datatype definition of combinators S and K, with infixed application **)
consts comb :: i
datatype
  "comb" = K
         | S
         | "#" ("p \\<in> comb", "q \\<in> comb")   (infixl 90)

(** Inductive definition of contractions, -1->
             and (multi-step) reductions, --->
**)
consts
  contract  :: i
  "-1->"    :: [i,i] => o                       (infixl 50)
  "--->"    :: [i,i] => o                       (infixl 50)

translations
  "p -1-> q" == "<p,q> \\<in> contract"
  "p ---> q" == "<p,q> \\<in> contract^*"

inductive
  domains   "contract" <= "comb*comb"
  intrs
    K     "[| p \\<in> comb;  q \\<in> comb |] ==> K#p#q -1-> p"
    S     "[| p \\<in> comb;  q \\<in> comb;  r \\<in> comb |] ==> S#p#q#r -1-> (p#r)#(q#r)"
    Ap1   "[| p-1->q;  r \\<in> comb |] ==> p#r -1-> q#r"
    Ap2   "[| p-1->q;  r \\<in> comb |] ==> r#p -1-> r#q"
  type_intrs "comb.intrs"


(** Inductive definition of parallel contractions, =1=>
             and (multi-step) parallel reductions, ===>
**)
consts
  parcontract :: i
  "=1=>"    :: [i,i] => o                       (infixl 50)
  "===>"    :: [i,i] => o                       (infixl 50)

translations
  "p =1=> q" == "<p,q> \\<in> parcontract"
  "p ===> q" == "<p,q> \\<in> parcontract^+"

inductive
  domains   "parcontract" <= "comb*comb"
  intrs
    refl  "[| p \\<in> comb |] ==> p =1=> p"
    K     "[| p \\<in> comb;  q \\<in> comb |] ==> K#p#q =1=> p"
    S     "[| p \\<in> comb;  q \\<in> comb;  r \\<in> comb |] ==> S#p#q#r =1=> (p#r)#(q#r)"
    Ap    "[| p=1=>q;  r=1=>s |] ==> p#r =1=> q#s"
  type_intrs "comb.intrs"


(*Misc definitions*)
constdefs
  I :: i
  "I == S#K#K"

  diamond :: i => o
  "diamond(r) == \\<forall>x y. <x,y>:r --> 
                          (\\<forall>y'. <x,y'>:r --> 
                                   (\\<exists>z. <y,z>:r & <y',z> \\<in> r))"

end
