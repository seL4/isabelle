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
    "JOIN I F == mk_program (INT i:I. Init (F i), UN i:I. Acts (F i))"

  Join :: ['a program, 'a program] => 'a program      (infixl 65)
    "F Join G == mk_program (Init F Int Init G, Acts F Un Acts G)"

  SKIP :: 'a program
    "SKIP == mk_program (UNIV, {})"

  Diff :: "['a program, ('a * 'a)set set] => 'a program"
    "Diff F acts == mk_program (Init F, Acts F - acts)"

  (*The set of systems that regard "f" as local to F*)
  localTo :: ['a => 'b, 'a program] => 'a program set  (infixl 80)
    "f localTo F == {G. ALL z. Diff G (Acts F) : stable {s. f s = z}}"

syntax
  "@JOIN"      :: [pttrn, 'a set, 'b set] => 'b set  ("(3JN _:_./ _)" 10)

translations
  "JN x:A. B"   == "JOIN A (%x. B)"

end
