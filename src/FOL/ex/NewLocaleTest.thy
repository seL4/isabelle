(*  Title:      FOL/ex/NewLocaleTest.thy
    ID:         $Id$
    Author:     Clemens Ballarin, TU Muenchen

Testing environment for locale expressions --- experimental.
*)

theory NewLocaleTest
imports NewLocaleSetup
begin

ML_val {* set new_locales *}
ML_val {* set Toplevel.debug *}
ML_val {* set show_hyps *}


typedecl int arities int :: "term"
consts plus :: "int => int => int" (infixl "+" 60)
  zero :: int ("0")
  minus :: "int => int" ("- _")


text {* Inference of parameter types *}

locale param1 = fixes p
print_locale! param1

locale param2 = fixes p :: 'b
print_locale! param2

(*
locale param_top = param2 r for r :: "'b :: {}"
print_locale! param_top
*)

locale param3 = fixes p (infix ".." 50)
print_locale! param3

locale param4 = fixes p :: "'a => 'a => 'a" (infix ".." 50)
print_locale! param4


text {* Incremental type constraints *}

locale constraint1 =
  fixes  prod (infixl "**" 65)
  assumes l_id: "x ** y = x"
  assumes assoc: "(x ** y) ** z = x ** (y ** z)"
print_locale! constraint1

locale constraint2 =
  fixes p and q
  assumes "p = q"
print_locale! constraint2


text {* Inheritance *}

locale semi =
  fixes prod (infixl "**" 65)
  assumes assoc: "(x ** y) ** z = x ** (y ** z)"
    and comm: "x ** y = y ** x"
print_locale! semi thm semi_def

locale lgrp = semi +
  fixes one and inv
  assumes lone: "one ** x = x"
    and linv: "inv(x) ** x = one"
print_locale! lgrp thm lgrp_def lgrp_axioms_def

locale add_lgrp = semi "op ++" for sum (infixl "++" 60) +
  fixes zero and neg
  assumes lzero: "zero ++ x = x"
    and lneg: "neg(x) ++ x = zero"
print_locale! add_lgrp thm add_lgrp_def add_lgrp_axioms_def

locale rev_lgrp = semi "%x y. y ++ x" for sum (infixl "++" 60)
print_locale! rev_lgrp thm rev_lgrp_def

locale hom = f: semi f + g: semi g for f and g
print_locale! hom thm hom_def

locale perturbation = semi + d: semi "%x y. delta(x) ** delta(y)" for delta
print_locale! perturbation thm perturbation_def

locale pert_hom = d1: perturbation f d1 + d2: perturbation f d2 for f d1 d2
print_locale! pert_hom thm pert_hom_def

text {* Alternative expression, obtaining nicer names in @{text "semi f"}. *}
locale pert_hom' = semi f + d1: perturbation f d1 + d2: perturbation f d2 for f d1 d2
print_locale! pert_hom' thm pert_hom'_def


text {* Syntax declarations *}

locale logic =
  fixes land (infixl "&&" 55)
    and lnot ("-- _" [60] 60)
  assumes assoc: "(x && y) && z = x && (y && z)"
    and notnot: "-- (-- x) = x"
begin

definition lor (infixl "||" 50) where
  "x || y = --(-- x && -- y)"

end
print_locale! logic

locale use_decl = logic + semi "op ||"
print_locale! use_decl thm use_decl_def


text {* Theorem statements *}

lemma (in lgrp) lcancel:
  "x ** y = x ** z <-> y = z"
proof
  assume "x ** y = x ** z"
  then have "inv(x) ** x ** y = inv(x) ** x ** z" by (simp add: assoc)
  then show "y = z" by (simp add: lone linv)
qed simp
print_locale! lgrp


locale rgrp = semi +
  fixes one and inv
  assumes rone: "x ** one = x"
    and rinv: "x ** inv(x) = one"
begin

lemma rcancel:
  "y ** x = z ** x <-> y = z"
proof
  assume "y ** x = z ** x"
  then have "y ** (x ** inv(x)) = z ** (x ** inv(x))"
    by (simp add: assoc [symmetric])
  then show "y = z" by (simp add: rone rinv)
qed simp

end
print_locale! rgrp

end
