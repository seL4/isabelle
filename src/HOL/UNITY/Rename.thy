(*  Title:      HOL/UNITY/Rename.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Renaming of state sets
*)

Rename = Extend +

constdefs
  
  rename :: "['a => 'b, 'a program] => 'b program"
    "rename h == extend (%(x,u::unit). h x)"

end
