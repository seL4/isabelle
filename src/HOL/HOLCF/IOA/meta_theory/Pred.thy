(*  Title:      HOL/HOLCF/IOA/meta_theory/Pred.thy
    Author:     Olaf Müller
*)

section \<open>Logical Connectives lifted to predicates\<close>

theory Pred
imports Main
begin

default_sort type

type_synonym
  'a predicate = "'a => bool"

consts

satisfies    ::"'a  => 'a predicate => bool"    ("_ \<Turnstile> _" [100,9] 8)
valid        ::"'a predicate => bool"           (*  ("|-") *)

NOT          ::"'a predicate => 'a predicate"  ("\<^bold>\<not> _" [40] 40)
AND          ::"'a predicate => 'a predicate => 'a predicate"    (infixr "\<^bold>\<and>" 35)
OR           ::"'a predicate => 'a predicate => 'a predicate"    (infixr "\<^bold>\<or>" 30)
IMPLIES      ::"'a predicate => 'a predicate => 'a predicate"    (infixr "\<^bold>\<longrightarrow>" 25)


defs

satisfies_def:
   "s \<Turnstile> P  == P s"

valid_def:
   "valid P == (! s. (s \<Turnstile> P))"

NOT_def:
  "NOT P s ==  ~ (P s)"

AND_def:
  "(P \<^bold>\<and> Q) s == (P s) & (Q s)"

OR_def:
  "(P \<^bold>\<or> Q) s ==  (P s) | (Q s)"

IMPLIES_def:
  "(P \<^bold>\<longrightarrow> Q) s == (P s) --> (Q s)"

end
