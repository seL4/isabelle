(*  Title:      Cube/Base.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993  University of Cambridge

Barendregt's Lambda-Cube.
*)

Base = Pure +

types
  term

types
  context  typing
nonterminals
  context_ typing_

consts
  Abs, Prod     :: "[term, term => term] => term"
  Trueprop      :: "[context, typing] => prop"
  MT_context    :: "context"
  Context       :: "[typing, context] => context"
  star          :: "term"                               ("*")
  box           :: "term"                               ("[]")
  "^"           :: "[term, term] => term"               (infixl 20)
  Has_type      :: "[term, term] => typing"

syntax
  Trueprop      :: "[context_, typing_] => prop"        ("(_/ |- _)")
  Trueprop1     :: "typing_ => prop"                    ("(_)")
  ""            :: "id => context_"                     ("_")
  ""            :: "var => context_"                    ("_")
  MT_context    :: "context_"                           ("")
  Context       :: "[typing_, context_] => context_"    ("_ _")
  Has_type      :: "[term, term] => typing_"            ("(_:/ _)" [0, 0] 5)
  Lam           :: "[idt, term, term] => term"          ("(3Lam _:_./ _)" [0, 0, 0] 10)
  Pi            :: "[idt, term, term] => term"          ("(3Pi _:_./ _)" [0, 0] 10)
  "->"          :: "[term, term] => term"               (infixr 10)

translations
  (prop) "x:X"  == (prop) "|- x:X"
  "Lam x:A. B"  == "Abs(A, %x. B)"
  "Pi x:A. B"   => "Prod(A, %x. B)"
  "A -> B"      => "Prod(A, _K(B))"

syntax (xsymbols)
  Trueprop      :: "[context_, typing_] => prop"        ("(_/ \\<turnstile> _)")
  box           :: "term"                               ("\\<box>")
  Lam           :: "[idt, term, term] => term"          ("(3\\<Lambda>_:_./ _)" [0, 0, 0] 10)
  Pi            :: "[idt, term, term] => term"          ("(3\\<Pi>_:_./ _)" [0, 0] 10)
  "op ->"       :: "[term, term] => term"               (infixr "\\<rightarrow>" 10)


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

