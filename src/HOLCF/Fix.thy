(*  Title: 	HOLCF/fix.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen


definitions for fixed point operator and admissibility

*)

Fix = Cfun3 +

consts

iterate :: "nat=>('a->'a)=>'a=>'a"
Ifix    :: "('a->'a)=>'a"
fix     :: "('a->'a)->'a"
adm          :: "('a=>bool)=>bool"
admw         :: "('a=>bool)=>bool"
chain_finite :: "'a=>bool"
flat         :: "'a=>bool"

rules

iterate_def   "iterate(n,F,c) == nat_rec(n,c,%n x.F[x])"
Ifix_def      "Ifix(F) == lub(range(%i.iterate(i,F,UU)))"
fix_def       "fix == (LAM f. Ifix(f))"

adm_def       "adm(P) == !Y. is_chain(Y) --> \
\                        (!i.P(Y(i))) --> P(lub(range(Y)))"

admw_def      "admw(P)== (!F.((!n.P(iterate(n,F,UU)))-->\
\			 P(lub(range(%i.iterate(i,F,UU))))))" 

chain_finite_def  "chain_finite(x::'a)==\
\                        !Y. is_chain(Y::nat=>'a) --> (? n.max_in_chain(n,Y))"

flat_def          "flat(x::'a) ==\
\                        ! x y. (x::'a) << y --> (x = UU) | (x=y)"

end

