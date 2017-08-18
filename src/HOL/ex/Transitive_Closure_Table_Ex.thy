(* Author: Stefan Berghofer, Lukas Bulwahn, TU Muenchen *)

section \<open>Simple example for table-based implementation of the reflexive transitive closure\<close>

theory Transitive_Closure_Table_Ex
imports "HOL-Library.Transitive_Closure_Table"
begin

datatype ty = A | B | C

inductive test :: "ty \<Rightarrow> ty \<Rightarrow> bool"
where
  "test A B"
| "test B A"
| "test B C"


text \<open>Invoking with the predicate compiler and the generic code generator\<close>

code_pred test .

values "{x. test\<^sup>*\<^sup>* A C}"
values "{x. test\<^sup>*\<^sup>* C A}"
values "{x. test\<^sup>*\<^sup>* A x}"
values "{x. test\<^sup>*\<^sup>* x C}"

value [nbe] "test\<^sup>*\<^sup>* A C"
value [nbe] "test\<^sup>*\<^sup>* C A"

end
