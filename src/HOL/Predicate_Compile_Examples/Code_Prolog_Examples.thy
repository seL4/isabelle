theory Code_Prolog_Examples
imports Predicate_Compile_Alternative_Defs
uses "~~/src/HOL/Tools/Predicate_Compile/code_prolog.ML"
begin

section {* Example append *}

inductive append
where
  "append [] ys ys"
| "append xs ys zs ==> append (x # xs) ys (x # zs)"

code_pred append .

values 3 "{((x::'b list), y, z). append x y z}"

end
