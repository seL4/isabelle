(*  Title: 	FOLP/ex/nat.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Examples for the manual "Introduction to Isabelle"

Theory of the natural numbers: Peano's axioms, primitive recursion
*)

Nat = IFOLP +
types   nat
arities nat         :: term
consts  "0"         :: "nat"    ("0")
        Suc         :: "nat=>nat"
        rec         :: "[nat, 'a, [nat,'a]=>'a] => 'a"
        "+"         :: "[nat, nat] => nat"              (infixl 60)

  (*Proof terms*)
       nrec         :: "[nat,p,[nat,p]=>p]=>p"
       ninj,nneq    :: "p=>p"
       rec0, recSuc :: "p"

rules   
  induct     "[| b:P(0); !!x u. u:P(x) ==> c(x,u):P(Suc(x)) 
             |] ==> nrec(n,b,c):P(n)"
  
  Suc_inject "p:Suc(m)=Suc(n) ==> ninj(p) : m=n"
  Suc_neq_0  "p:Suc(m)=0      ==> nneq(p) : R"
  rec_0      "rec0 : rec(0,a,f) = a"
  rec_Suc    "recSuc : rec(Suc(m), a, f) = f(m, rec(m,a,f))"
  add_def    "m+n == rec(m, n, %x y. Suc(y))"

  nrecB0     "b: A ==> nrec(0,b,c) = b : A"
  nrecBSuc   "c(n,nrec(n,b,c)) : A ==> nrec(Suc(n),b,c) = c(n,nrec(n,b,c)) : A"
end
