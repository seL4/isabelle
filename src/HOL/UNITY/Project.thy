(*  Title:      HOL/UNITY/Project.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Projections of state sets (also of actions and programs)

Inheritance of GUARANTEES properties under extension
*)

Project = Extend +

constdefs
  projecting :: "['c program => 'c set, 'a*'b => 'c, 
		  'a program, 'c program set, 'a program set] => bool"
  "projecting C h F X' X ==
     ALL G. extend h F Join G : X' --> F Join project h (C G) G : X"

  extending :: "['c=>'d, 'c program => 'c set, 'a*'b => 'c, 'a program, 
		 'c program set, 'a program set] => bool"
  "extending v C h F Y' Y ==
     ALL G. G : preserves v --> F Join project h (C G) G : Y
            --> extend h F Join G : Y'"

end
