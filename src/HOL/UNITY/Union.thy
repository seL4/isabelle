(*  Title:      HOL/UNITY/Union.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Unions of programs

From Misra's Chapter 5: Asynchronous Compositions of Programs
*)

Union = SubstAx + FP +

constdefs

   Join :: ['a program, 'a program] => 'a program
    "Join prgF prgG == (|Init = Init prgF Int Init prgG,
			 Acts = Acts prgF Un Acts prgG|)"

   Null :: 'a program
    "Null == (|Init = UNIV, Acts = {id}|)"

end
