(*  Title:      HOL/UNITY/Union.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Unions of programs

From Misra's Chapter 5: Asynchronous Compositions of Programs
*)

Union = SubstAx + FP +

constdefs
   JOIN  :: ['a set, 'a => 'b program] => 'b program
    "JOIN I prg == mk_program (INT i:I. Init (prg i),
			       UN  i:I. Acts (prg i))"

   Join :: ['a program, 'a program] => 'a program
    "Join prgF prgG == mk_program (Init prgF Int Init prgG,
				   Acts prgF Un Acts prgG)"

   SKIP :: 'a program
    "SKIP == mk_program (UNIV, {})"

syntax
  "@JOIN"      :: [pttrn, 'a set, 'b set] => 'b set  ("(3JN _:_./ _)" 10)

translations
  "JN x:A. B"   == "JOIN A (%x. B)"

end
