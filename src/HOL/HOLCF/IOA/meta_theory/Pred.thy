(*  Title:      HOL/HOLCF/IOA/meta_theory/Pred.thy
    Author:     Olaf Müller
*)

section {* Logical Connectives lifted to predicates *}

theory Pred
imports Main
begin

default_sort type

type_synonym
  'a predicate = "'a => bool"

consts

satisfies    ::"'a  => 'a predicate => bool"    ("_ |= _" [100,9] 8)
valid        ::"'a predicate => bool"           (*  ("|-") *)

NOT          ::"'a predicate => 'a predicate"  (".~ _" [40] 40)
AND          ::"'a predicate => 'a predicate => 'a predicate"    (infixr ".&" 35)
OR           ::"'a predicate => 'a predicate => 'a predicate"    (infixr ".|" 30)
IMPLIES      ::"'a predicate => 'a predicate => 'a predicate"    (infixr ".-->" 25)


notation (output)
  NOT  ("~ _" [40] 40) and
  AND  (infixr "&" 35) and
  OR  (infixr "|" 30) and
  IMPLIES  (infixr "-->" 25)

notation (xsymbols output)
  NOT  ("\<not> _" [40] 40) and
  AND  (infixr "\<and>" 35) and
  OR  (infixr "\<or>" 30) and
  IMPLIES  (infixr "\<longrightarrow>" 25)

notation (xsymbols)
  satisfies  ("_ \<Turnstile> _" [100,9] 8)

notation (HTML output)
  NOT  ("\<not> _" [40] 40) and
  AND  (infixr "\<and>" 35) and
  OR  (infixr "\<or>" 30)


defs

satisfies_def:
   "s |= P  == P s"

(* priority einfuegen, da clash mit |=, wenn graphisches Symbol *)
valid_def:
   "valid P == (! s. (s |= P))"

NOT_def:
  "NOT P s ==  ~ (P s)"

AND_def:
  "(P .& Q) s == (P s) & (Q s)"

OR_def:
  "(P .| Q) s ==  (P s) | (Q s)"

IMPLIES_def:
  "(P .--> Q) s == (P s) --> (Q s)"

end
