(*  Title:      HOL/UNITY/Rename.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Renaming of state sets
*)

Rename = Extend +

constdefs
  rename_act :: "['a => 'b, ('a*'a) set] => ('b*'b) set"
    "rename_act h == extend_act (%(x,u::unit). h x)"

(**OR
      "rename_act h == %act. UN (s,s'): act.  {(h s, h s')}"
      "rename_act h == %act. (prod_fun h h) `` act"
**)
  
  rename :: "['a => 'b, 'a program] => 'b program"
    "rename h == extend (%(x,u::unit). h x)"

end
