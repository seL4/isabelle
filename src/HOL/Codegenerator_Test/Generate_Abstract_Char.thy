
(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Pervasive test of code generator\<close>

theory Generate_Abstract_Char
imports
  Candidates
  "HOL-Library.Code_Abstract_Char"
begin

text \<open>
  If any of the checks fails, inspect the code generated
  by a corresponding \<open>export_code\<close> command.
\<close>

export_code _ checking SML OCaml? Haskell? Scala

end
