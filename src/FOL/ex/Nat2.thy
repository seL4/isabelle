(*  Title: 	FOL/ex/nat2.thy
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1994  University of Cambridge

Theory for examples of simplification and induction on the natural numbers
*)

Nat2 = FOL +

types nat
arities nat :: term

consts
 succ,pred :: "nat => nat"
       "0" :: "nat"	("0")
       "+" :: "[nat,nat] => nat" (infixr 90)
  "<","<=" :: "[nat,nat] => o"   (infixr 70)

rules
 pred_0		"pred(0) = 0"
 pred_succ	"pred(succ(m)) = m"

 plus_0		"0+n = n"
 plus_succ	"succ(m)+n = succ(m+n)"

 nat_distinct1	"~ 0=succ(n)"
 nat_distinct2	"~ succ(m)=0"
 succ_inject	"succ(m)=succ(n) <-> m=n"

 leq_0		"0 <= n"
 leq_succ_succ	"succ(m)<=succ(n) <-> m<=n"
 leq_succ_0	"~ succ(m) <= 0"

 lt_0_succ	"0 < succ(n)"
 lt_succ_succ	"succ(m)<succ(n) <-> m<n"
 lt_0 "~ m < 0"

 nat_ind	"[| P(0); ALL n. P(n)-->P(succ(n)) |] ==> All(P)"
end
