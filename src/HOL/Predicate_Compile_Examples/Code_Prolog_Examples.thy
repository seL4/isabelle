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

ML {*
  tracing (Code_Prolog.write_program (Code_Prolog.generate @{context} [@{const_name append}]))
*}

ML {*
  Code_Prolog.run (Code_Prolog.generate @{context} [@{const_name append}]) "append" ["X", "Y", "Z"]
*}

end
