(*  Title: 	FOL/ex/nat.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Examples for the manual "Introduction to Isabelle"

Theory of the natural numbers: Peano's axioms, primitive recursion

INCOMPATIBLE with nat2.thy, Nipkow's example
*)

Nat = FOL +
types   nat 0
arities nat         :: term
consts  "0"         :: "nat"    ("0")
        Suc         :: "nat=>nat"
        rec         :: "[nat, 'a, [nat,'a]=>'a] => 'a"
        "+"         :: "[nat, nat] => nat"              (infixl 60)
rules   induct      "[| P(0);  !!x. P(x) ==> P(Suc(x)) |]  ==> P(n)"
        Suc_inject  "Suc(m)=Suc(n) ==> m=n"
        Suc_neq_0   "Suc(m)=0      ==> R"
        rec_0       "rec(0,a,f) = a"
        rec_Suc     "rec(Suc(m), a, f) = f(m, rec(m,a,f))"
        add_def     "m+n == rec(m, n, %x y. Suc(y))"
end
