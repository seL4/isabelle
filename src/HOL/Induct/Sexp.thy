(*  Title:      HOL/Induct/Sexp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

S-expressions, general binary trees for defining recursive data
structures by hand.
*)

Sexp = Datatype_Universe + Inductive +
consts
  sexp      :: 'a item set

  sexp_case :: "['a=>'b, nat=>'b, ['a item, 'a item]=>'b, 
                'a item] => 'b"

  sexp_rec  :: "['a item, 'a=>'b, nat=>'b,      
                ['a item, 'a item, 'b, 'b]=>'b] => 'b"
  
  pred_sexp :: "('a item * 'a item)set"

inductive sexp
  intrs
    LeafI  "Leaf(a): sexp"
    NumbI  "Numb(i): sexp"
    SconsI "[| M: sexp;  N: sexp |] ==> Scons M N : sexp"

defs

  sexp_case_def 
   "sexp_case c d e M == @ z. (? x.   M=Leaf(x) & z=c(x))  
                            | (? k.   M=Numb(k) & z=d(k))  
                            | (? N1 N2. M = Scons N1 N2  & z=e N1 N2)"

  pred_sexp_def
     "pred_sexp == UN M: sexp. UN N: sexp. {(M, Scons M N), (N, Scons M N)}"

  sexp_rec_def
   "sexp_rec M c d e == wfrec pred_sexp
             (%g. sexp_case c d (%N1 N2. e N1 N2 (g N1) (g N2))) M"
end
