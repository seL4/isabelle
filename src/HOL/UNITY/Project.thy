(*  Title:      HOL/UNITY/Project.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Projections of state sets (also of actions and programs)

Inheritance of GUARANTEES properties under extension
*)

Project = Extend +


constdefs

  restr_act :: "['c set, 'a*'b => 'c, ('a*'a) set] => ('a*'a) set"
    "restr_act C h act == project_act C h (extend_act h act)"

  restr :: "['c set, 'a*'b => 'c, 'a program] => 'a program"
    "restr C h F == project C h (extend h F)"

end
