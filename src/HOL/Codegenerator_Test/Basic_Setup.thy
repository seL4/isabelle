(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Basic setup\<close>

theory Basic_Setup
imports
  Complex_Main
begin

text \<open>Drop technical stuff from \<^theory>\<open>HOL.Quickcheck_Narrowing\<close> which is tailored towards Haskell\<close>

ML \<open>
structure Codegenerator_Test =
struct

fun drop_partial_term_of thy =
  let
    val tycos = Sign.logical_types thy;
    val consts = map_filter (try (curry (Axclass.param_of_inst thy)
      \<^const_name>\<open>Quickcheck_Narrowing.partial_term_of\<close>)) tycos;
  in
    thy
    |> fold Code.declare_unimplemented_global consts
  end;

end;
\<close>

text \<open>Avoid popular infix.\<close>

code_reserved (SML) upto

end
