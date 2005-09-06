(*  Title:      FOL/ex/NatClass.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

theory NatClass
imports FOL
begin

text {*
  This is an abstract version of theory @{text "Nat"}. Instead of
  axiomatizing a single type @{text nat} we define the class of all
  these types (up to isomorphism).

  Note: The @{text rec} operator had to be made \emph{monomorphic},
  because class axioms may not contain more than one type variable.
*}

consts
  0 :: 'a    ("0")
  Suc :: "'a => 'a"
  rec :: "['a, 'a, ['a, 'a] => 'a] => 'a"

axclass
  nat < "term"
  induct:        "[| P(0); !!x. P(x) ==> P(Suc(x)) |] ==> P(n)"
  Suc_inject:    "Suc(m) = Suc(n) ==> m = n"
  Suc_neq_0:     "Suc(m) = 0 ==> R"
  rec_0:         "rec(0, a, f) = a"
  rec_Suc:       "rec(Suc(m), a, f) = f(m, rec(m, a, f))"

constdefs
  add :: "['a::nat, 'a] => 'a"    (infixl "+" 60)
  "m + n == rec(m, n, %x y. Suc(y))"

ML {* use_legacy_bindings (the_context ()) *}
ML {* open nat_class *}

end
