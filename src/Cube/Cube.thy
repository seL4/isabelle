(*  Title:      Cube/cube.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993  University of Cambridge

Barendregt's Lambda-Cube
*)

Cube = Pure +

types
  term  context  typing

arities
  term :: logic

consts
  Abs, Prod     :: "[term, term => term] => term"
  Trueprop      :: "[context, typing] => prop"          ("(_/ |- _)")
  MT_context    :: "context"                            ("")
  Context       :: "[typing, context] => context"       ("_ _")
  star          :: "term"                               ("*")
  box           :: "term"                               ("[]")
  "^"           :: "[term, term] => term"               (infixl 20)
  "->"          :: "[term, term] => term"               (infixr 10)
  Has_type      :: "[term, term] => typing"             ("(_:/ _)" [0, 0] 5)

syntax
  Trueprop1     :: "typing => prop"                     ("(_)")
  ""            :: "id => context"                      ("_ ")
  ""            :: "var => context"                     ("_ ")
  Lam           :: "[idt, term, term] => term"          ("(3Lam _:_./ _)" [0, 0, 0] 10)
  Pi            :: "[idt, term, term] => term"          ("(3Pi _:_./ _)" [0, 0] 10)

translations
  (prop) "x:X"  == (prop) "|- x:X"
  "Lam x:A. B"  == "Abs(A, %x. B)"
  "Pi x:A. B"   => "Prod(A, %x. B)"
  "A -> B"      => "Prod(A, _K(B))"

rules
  s_b           "*: []"

  strip_s       "[| A:*;  a:A ==> G |- x:X |] ==> a:A G |- x:X"
  strip_b       "[| A:[]; a:A ==> G |- x:X |] ==> a:A G |- x:X"

  app           "[| F:Prod(A, B); C:A |] ==> F^C: B(C)"

  pi_ss         "[| A:*; !!x. x:A ==> B(x):* |] ==> Prod(A, B):*"

  lam_ss        "[| A:*; !!x. x:A ==> f(x):B(x); !!x. x:A ==> B(x):* |] 
                   ==> Abs(A, f) : Prod(A, B)"

  beta          "Abs(A, f)^a == f(a)"

end


ML

val print_translation = [("Prod", dependent_tr' ("Pi", "op ->"))];

