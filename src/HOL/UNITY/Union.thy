(*  Title:      HOL/UNITY/Union.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Unions of programs

Partly from Misra's Chapter 5: Asynchronous Compositions of Programs

Do we need a Meet operator?  (Aka Intersection)
*)

Union = SubstAx + FP +

constdefs
  JOIN  :: ['a set, 'a => 'b program] => 'b program
    "JOIN I F == mk_program (INT i:I. Init (F i), UN i:I. Acts (F i))"

  Join :: ['a program, 'a program] => 'a program      (infixl 65)
    "F Join G == mk_program (Init F Int Init G, Acts F Un Acts G)"

  SKIP :: 'a program
    "SKIP == mk_program (UNIV, {})"

  Diff :: "['a set, 'a program, ('a * 'a)set set] => 'a program"
    "Diff C G acts ==
       mk_program (Init G, (Restrict C `` Acts G) - (Restrict C `` acts))"

  (*The set of systems that regard "v" as local to F*)
  LOCALTO :: ['a => 'b, 'a set, 'a program] => 'a program set
                                           ("(_/ localTo[_]/ _)" [80,0,80] 80)
    "v localTo[C] F == {G. ALL z. Diff C G (Acts F) : stable {s. v s = z}}"

  (*The weak version of localTo, considering only G's reachable states*)
  LocalTo :: ['a => 'b, 'a program] => 'a program set  (infixl 80)
    "v LocalTo F == {G. G : v localTo[reachable G] F}"

  (*Two programs with disjoint actions, except for identity actions.
    It's a weak property but still useful.*)
  Disjoint :: ['a set, 'a program, 'a program] => bool
    "Disjoint C F G ==
       (Restrict C `` (Acts F - {Id})) Int (Restrict C `` (Acts G - {Id}))
       <= {}"

syntax
  "@JOIN1"     :: [pttrns, 'b set] => 'b set         ("(3JN _./ _)" 10)
  "@JOIN"      :: [pttrn, 'a set, 'b set] => 'b set  ("(3JN _:_./ _)" 10)

translations
  "JN x:A. B"   == "JOIN A (%x. B)"
  "JN x y. B"   == "JN x. JN y. B"
  "JN x. B"     == "JOIN UNIV (%x. B)"

end
