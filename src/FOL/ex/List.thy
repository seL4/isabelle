(*  Title: 	FOL/ex/list
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1991  University of Cambridge

Examples of simplification and induction on lists
*)

List = Nat2 +

types 'a list
arities list :: (term)term

consts
   hd		:: "'a list => 'a"
   tl		:: "'a list => 'a list"
   forall	:: "['a list, 'a => o] => o"
   len		:: "'a list => nat"
   at		:: "['a list, nat] => 'a"
   "[]"		:: "'a list"	("[]")
   "."		:: "['a, 'a list] => 'a list"  (infixr 80)
   "++"		:: "['a list, 'a list] => 'a list" (infixr 70)

rules
 list_ind "[| P([]);  ALL x l. P(l)-->P(x.l) |] ==> All(P)"

 forall_cong 
  "[| l = l';  !!x. P(x)<->P'(x) |] ==> forall(l,P) <-> forall(l',P')"

 list_distinct1 "~[] = x.l"
 list_distinct2 "~x.l = []"

 list_free 	"x.l = x'.l' <-> x=x' & l=l'"

 app_nil 	"[]++l = l"
 app_cons 	"(x.l)++l' = x.(l++l')"
 tl_eq 	"tl(m.q) = q"
 hd_eq 	"hd(m.q) = m"

 forall_nil "forall([],P)"
 forall_cons "forall(x.l,P) <-> P(x) & forall(l,P)"

 len_nil "len([]) = 0"
 len_cons "len(m.q) = succ(len(q))"

 at_0 "at(m.q,0) = m"
 at_succ "at(m.q,succ(n)) = at(q,n)"

end
