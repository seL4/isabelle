(*  Title:	BijectionRel.thy
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge
*)

BijectionRel = Main +

consts
  bijR :: "(['a, 'b] => bool) => ('a set * 'b set) set"

inductive "bijR P"
intrs
  empty  "({},{}) : bijR P"
  insert "[| P a b; a ~: A; b ~: B; (A,B) : bijR P |] \ 
\        ==> (insert a A, insert b B) : bijR P" 

(* Add extra condition to insert: ALL b:B. ~(P a b) (and similar for A) *) 

consts
  bijP :: "(['a, 'a] => bool) => 'a set => bool"

defs
  bijP_def "bijP P F == (ALL a b. a:F & P a b --> b:F)" 

consts
  uniqP :: "(['a, 'a] => bool) => bool"
  symP :: "(['a, 'a] => bool) => bool"
  
defs
  uniqP_def "uniqP P == (ALL a b c d. P a b & P c d --> (a=c) = (b=d))" 
  symP_def  "symP P  == (ALL a b. (P a b) = (P b a))" 

consts
  bijER :: "(['a, 'a] => bool) => 'a set set"

inductive "bijER P"
intrs
  empty   "{} : bijER P"
  insert1 "[| P a a; a ~: A; A : bijER P |] \ 
\         ==> (insert a A) : bijER P" 
  insert2 "[| P a b; a ~= b; a ~: A; b ~: A; A : bijER P |] \ 
\         ==> (insert a (insert b A)) : bijER P" 

end

