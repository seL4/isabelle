(*  Title:      HOLCF/Fix.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen


definitions for fixed point operator and admissibility

*)

Fix = Cfun3 +

consts

iterate	:: "nat=>('a->'a)=>'a=>'a"
Ifix	:: "('a->'a)=>'a"
fix	:: "('a->'a)->'a"
adm		:: "('a::cpo=>bool)=>bool"
admw		:: "('a=>bool)=>bool"

defs

iterate_def   "iterate n F c == nat_rec c (%n x. F`x) n"
Ifix_def      "Ifix F == lub(range(%i. iterate i F UU))"
fix_def       "fix == (LAM f. Ifix f)"

adm_def       "adm P == !Y. chain(Y) --> 
                        (!i. P(Y i)) --> P(lub(range Y))"

admw_def      "admw P == !F. (!n. P (iterate n F UU)) -->
                            P (lub(range (%i. iterate i F UU)))" 

end

