(*  Title:      ZF/UNITY/Union.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Unions of programs

Partly from Misra's Chapter 5: Asynchronous Compositions of Programs

Theory ported form HOL..

*)

Union = SubstAx + FP +

constdefs

  (*FIXME: conjoin Init(F) Int Init(G) ~= 0 *) 
  ok :: [i, i] => o     (infixl 65)
    "F ok G == Acts(F) <= AllowedActs(G) &
               Acts(G) <= AllowedActs(F)"

  (*FIXME: conjoin (INT i:I. Init(F(i))) ~= 0 *) 
  OK  :: [i, i=>i] => o
    "OK(I,F) == (ALL i:I. ALL j: I-{i}. Acts(F(i)) <= AllowedActs(F(j)))"

   JOIN  :: [i, i=>i] => i
  "JOIN(I,F) == if I = 0 then SKIP else
                 mk_program(INT i:I. Init(F(i)), UN i:I. Acts(F(i)),
                 INT i:I. AllowedActs(F(i)))"

  Join :: [i, i] => i    (infixl 65)
  "F Join G == mk_program (Init(F) Int Init(G), Acts(F) Un Acts(G),
				AllowedActs(F) Int AllowedActs(G))"
  (*Characterizes safety properties.  Used with specifying AllowedActs*)
  safety_prop :: "i => o"
  "safety_prop(X) == X<=program &
      SKIP:X & (ALL G:program. Acts(G) <= (UN F:X. Acts(F)) --> G:X)"
  
syntax
  "@JOIN1"     :: [pttrns, i] => i         ("(3JN _./ _)" 10)
  "@JOIN"      :: [pttrn, i, i] => i       ("(3JN _:_./ _)" 10)

translations
  "JN x:A. B"   == "JOIN(A, (%x. B))"
  "JN x y. B"   == "JN x. JN y. B"
  "JN x. B"     == "JOIN(state,(%x. B))"

syntax (symbols)
   SKIP     :: i                    ("\\<bottom>")
  "op Join" :: [i, i] => i   (infixl "\\<squnion>" 65)
  "@JOIN1"  :: [pttrns, i] => i     ("(3\\<Squnion> _./ _)" 10)
  "@JOIN"   :: [pttrn, i, i] => i   ("(3\\<Squnion> _:_./ _)" 10)

end
