(*  Title:      HOL/UNITY/Union.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Unions of programs

Partly from Misra's Chapter 5: Asynchronous Compositions of Programs
*)

Union = SubstAx + FP +

constdefs

  (*FIXME: conjoin Init F Int Init G ~= {} *) 
  ok :: ['a program, 'a program] => bool      (infixl 65)
    "F ok G == Acts F <= AllowedActs G &
               Acts G <= AllowedActs F"

  (*FIXME: conjoin (INT i:I. Init (F i)) ~= {} *) 
  OK  :: ['a set, 'a => 'b program] => bool
    "OK I F == (ALL i:I. ALL j: I-{i}. Acts (F i) <= AllowedActs (F j))"

  JOIN  :: ['a set, 'a => 'b program] => 'b program
    "JOIN I F == mk_program (INT i:I. Init (F i), UN i:I. Acts (F i),
			     INT i:I. AllowedActs (F i))"

  Join :: ['a program, 'a program] => 'a program      (infixl 65)
    "F Join G == mk_program (Init F Int Init G, Acts F Un Acts G,
			     AllowedActs F Int AllowedActs G)"

  SKIP :: 'a program
    "SKIP == mk_program (UNIV, {}, UNIV)"

  (*Characterizes safety properties.  Used with specifying AllowedActs*)
  safety_prop :: "'a program set => bool"
    "safety_prop X == SKIP: X & (ALL G. Acts G <= UNION X Acts --> G : X)"

syntax
  "@JOIN1"     :: [pttrns, 'b set] => 'b set         ("(3JN _./ _)" 10)
  "@JOIN"      :: [pttrn, 'a set, 'b set] => 'b set  ("(3JN _:_./ _)" 10)

translations
  "JN x:A. B"   == "JOIN A (%x. B)"
  "JN x y. B"   == "JN x. JN y. B"
  "JN x. B"     == "JOIN UNIV (%x. B)"

syntax (symbols)
  SKIP      :: 'a program                              ("\\<bottom>")
  "op Join" :: ['a program, 'a program] => 'a program  (infixl "\\<squnion>" 65)
  "@JOIN1"  :: [pttrns, 'b set] => 'b set              ("(3\\<Squnion> _./ _)" 10)
  "@JOIN"   :: [pttrn, 'a set, 'b set] => 'b set       ("(3\\<Squnion> _:_./ _)" 10)

end
