(*  Title:      FOL/ex/Nat.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Examples for the manuals.

Theory of the natural numbers: Peano's axioms, primitive recursion
*)

Nat = LK +
types   nat
arities nat :: term
consts  "0" :: nat      ("0")
        Suc :: nat=>nat  
        rec :: [nat, 'a, [nat,'a]=>'a] => 'a  
        "+" :: [nat, nat] => nat                (infixl 60)

rules   
  induct      "[| $H |- $E, P(0), $F;
		  !!x. $H |- $E, P(x) --> P(Suc(x)), $F |] ==> $H |- $E, P(n), $F"
  Suc_inject  "|- Suc(m)=Suc(n) --> m=n"
  Suc_neq_0   "|- Suc(m) ~= 0"
  rec_0       "|- rec(0,a,f) = a"
  rec_Suc     "|- rec(Suc(m), a, f) = f(m, rec(m,a,f))"
  add_def     "m+n == rec(m, n, %x y. Suc(y))"
end
