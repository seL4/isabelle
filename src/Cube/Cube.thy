(*  Title:      Cube/Cube.thy
    Author:     Tobias Nipkow
*)

header {* Barendregt's Lambda-Cube *}

theory Cube
imports Pure
begin

setup Pure_Thy.old_appl_syntax_setup

typedecl "term"
typedecl "context"
typedecl typing

axiomatization
  Abs :: "[term, term => term] => term" and
  Prod :: "[term, term => term] => term" and
  Trueprop :: "[context, typing] => prop" and
  MT_context :: "context" and
  Context :: "[typing, context] => context" and
  star :: "term"  ("*") and
  box :: "term"  ("[]") and
  app :: "[term, term] => term"  (infixl "^" 20) and
  Has_type :: "[term, term] => typing"

notation (xsymbols)
  box  ("\<box>")

nonterminal context' and typing'

syntax
  "_Trueprop" :: "[context', typing'] => prop"  ("(_/ |- _)")
  "_Trueprop1" :: "typing' => prop"  ("(_)")
  "" :: "id => context'"  ("_")
  "" :: "var => context'"  ("_")
  "_MT_context" :: "context'"  ("")
  "_Context" :: "[typing', context'] => context'"  ("_ _")
  "_Has_type" :: "[term, term] => typing'"  ("(_:/ _)" [0, 0] 5)
  "_Lam" :: "[idt, term, term] => term"  ("(3Lam _:_./ _)" [0, 0, 0] 10)
  "_Pi" :: "[idt, term, term] => term"  ("(3Pi _:_./ _)" [0, 0] 10)
  "_arrow" :: "[term, term] => term"  (infixr "->" 10)

translations
  "_Trueprop(G, t)" == "CONST Trueprop(G, t)"
  ("prop") "x:X" == ("prop") "|- x:X"
  "_MT_context" == "CONST MT_context"
  "_Context" == "CONST Context"
  "_Has_type" == "CONST Has_type"
  "Lam x:A. B" == "CONST Abs(A, %x. B)"
  "Pi x:A. B" => "CONST Prod(A, %x. B)"
  "A -> B" => "CONST Prod(A, %_. B)"

syntax (xsymbols)
  "_Trueprop" :: "[context', typing'] => prop"    ("(_/ \<turnstile> _)")
  "_Lam" :: "[idt, term, term] => term"    ("(3\<Lambda> _:_./ _)" [0, 0, 0] 10)
  "_Pi" :: "[idt, term, term] => term"    ("(3\<Pi> _:_./ _)" [0, 0] 10)
  "_arrow" :: "[term, term] => term"    (infixr "\<rightarrow>" 10)

print_translation {*
  [(@{const_syntax Prod},
    Syntax_Trans.dependent_tr' (@{syntax_const "_Pi"}, @{syntax_const "_arrow"}))]
*}

axiomatization where
  s_b: "*: []"  and

  strip_s: "[| A:*;  a:A ==> G |- x:X |] ==> a:A G |- x:X" and
  strip_b: "[| A:[]; a:A ==> G |- x:X |] ==> a:A G |- x:X" and

  app: "[| F:Prod(A, B); C:A |] ==> F^C: B(C)" and

  pi_ss: "[| A:*; !!x. x:A ==> B(x):* |] ==> Prod(A, B):*" and

  lam_ss: "[| A:*; !!x. x:A ==> f(x):B(x); !!x. x:A ==> B(x):* |]
            ==> Abs(A, f) : Prod(A, B)" and

  beta: "Abs(A, f)^a == f(a)"

lemmas simple = s_b strip_s strip_b app lam_ss pi_ss
lemmas rules = simple

lemma imp_elim:
  assumes "f:A->B" and "a:A" and "f^a:B ==> PROP P"
  shows "PROP P" by (rule app assms)+

lemma pi_elim:
  assumes "F:Prod(A,B)" and "a:A" and "F^a:B(a) ==> PROP P"
  shows "PROP P" by (rule app assms)+


locale L2 =
  assumes pi_bs: "[| A:[]; !!x. x:A ==> B(x):* |] ==> Prod(A,B):*"
    and lam_bs: "[| A:[]; !!x. x:A ==> f(x):B(x); !!x. x:A ==> B(x):* |]
                   ==> Abs(A,f) : Prod(A,B)"

lemmas (in L2) rules = simple lam_bs pi_bs


locale Lomega =
  assumes
    pi_bb: "[| A:[]; !!x. x:A ==> B(x):[] |] ==> Prod(A,B):[]"
    and lam_bb: "[| A:[]; !!x. x:A ==> f(x):B(x); !!x. x:A ==> B(x):[] |]
                   ==> Abs(A,f) : Prod(A,B)"

lemmas (in Lomega) rules = simple lam_bb pi_bb


locale LP =
  assumes pi_sb: "[| A:*; !!x. x:A ==> B(x):[] |] ==> Prod(A,B):[]"
    and lam_sb: "[| A:*; !!x. x:A ==> f(x):B(x); !!x. x:A ==> B(x):[] |]
                   ==> Abs(A,f) : Prod(A,B)"
begin

lemmas rules = simple lam_sb pi_sb

end


locale LP2 = LP + L2
begin

lemmas rules = simple lam_bs pi_bs lam_sb pi_sb

end


locale Lomega2 = L2 + Lomega
begin

lemmas rules = simple lam_bs pi_bs lam_bb pi_bb

end


locale LPomega = LP + Lomega
begin

lemmas rules = simple lam_bb pi_bb lam_sb pi_sb

end


locale CC = L2 + LP + Lomega
begin

lemmas rules = simple lam_bs pi_bs lam_bb pi_bb lam_sb pi_sb

end

end
