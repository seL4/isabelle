(*  Title: 	ZF/ex/Comb.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson
    Copyright   1994  University of Cambridge

Combinatory Logic example: the Church-Rosser Theorem
Curiously, combinators do not include free variables.

Example taken from
    J. Camilleri and T. F. Melham.
    Reasoning with Inductively Defined Relations in the HOL Theorem Prover.
    Report 265, University of Cambridge Computer Laboratory, 1992.
*)


Comb = Univ + "Datatype" +

(** Datatype definition of combinators S and K, with infixed application **)
consts comb :: "i"
datatype (* <= "univ(0)" *)
  "comb" = K
         | S
         | "#" ("p: comb", "q: comb")   (infixl 90)

(** Inductive definition of contractions, -1->
             and (multi-step) reductions, --->
**)
consts
  contract  :: "i"
  "-1->"    :: "[i,i] => o"    			(infixl 50)
  "--->"    :: "[i,i] => o"    			(infixl 50)

translations
  "p -1-> q" == "<p,q> : contract"
  "p ---> q" == "<p,q> : contract^*"

inductive
  domains   "contract" <= "comb*comb"
  intrs
    K     "[| p:comb;  q:comb |] ==> K#p#q -1-> p"
    S     "[| p:comb;  q:comb;  r:comb |] ==> S#p#q#r -1-> (p#r)#(q#r)"
    Ap1   "[| p-1->q;  r:comb |] ==> p#r -1-> q#r"
    Ap2   "[| p-1->q;  r:comb |] ==> r#p -1-> r#q"
  type_intrs "comb.intrs"


(** Inductive definition of parallel contractions, =1=>
             and (multi-step) parallel reductions, ===>
**)
consts
  parcontract :: "i"
  "=1=>"    :: "[i,i] => o"    			(infixl 50)
  "===>"    :: "[i,i] => o"    			(infixl 50)

translations
  "p =1=> q" == "<p,q> : parcontract"
  "p ===> q" == "<p,q> : parcontract^+"

inductive
  domains   "parcontract" <= "comb*comb"
  intrs
    refl  "[| p:comb |] ==> p =1=> p"
    K     "[| p:comb;  q:comb |] ==> K#p#q =1=> p"
    S     "[| p:comb;  q:comb;  r:comb |] ==> S#p#q#r =1=> (p#r)#(q#r)"
    Ap    "[| p=1=>q;  r=1=>s |] ==> p#r =1=> q#s"
  type_intrs "comb.intrs"


(*Misc definitions*)
consts
  diamond   :: "i => o"
  I         :: "i"

defs

  diamond_def "diamond(r) == ALL x y. <x,y>:r --> \
\                            (ALL y'. <x,y'>:r --> \
\                                 (EX z. <y,z>:r & <y',z> : r))"

  I_def       "I == S#K#K"

end
