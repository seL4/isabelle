(*  Title:	WilsonRuss.thy
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge
*)

WilsonRuss = EulerFermat +

consts
  inv    :: "[int,int] => int" 
  wset   :: "int*int=>int set"

defs
  inv_def   "inv p a == (a ^ (nat (p - #2))) mod p"

recdef wset "measure ((%(a,p).(nat a)) ::int*int=>nat)"
    "wset (a,p) = (if #1<a then let ws = wset (a-#1,p) in
                     (if a:ws then ws else insert a (insert (inv p a) ws))
                   else {})"

end
