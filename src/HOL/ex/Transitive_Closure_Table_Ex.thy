(* Author: Stefan Berghofer, Lukas Bulwahn, TU Muenchen *)

section {* Simple example for table-based implementation of the reflexive transitive closure *}

theory Transitive_Closure_Table_Ex
imports "~~/src/HOL/Library/Transitive_Closure_Table"
begin

datatype ty = A | B | C

inductive test :: "ty \<Rightarrow> ty \<Rightarrow> bool"
where
  "test A B"
| "test B A"
| "test B C"


text {* Invoking with the predicate compiler and the generic code generator *}

code_pred test .

values "{x. test\<^sup>*\<^sup>* A C}"
values "{x. test\<^sup>*\<^sup>* C A}"
values "{x. test\<^sup>*\<^sup>* A x}"
values "{x. test\<^sup>*\<^sup>* x C}"

value "test\<^sup>*\<^sup>* A C"
value "test\<^sup>*\<^sup>* C A"

end
