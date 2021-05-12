(*  Title:      HOL/Mirabelle/Mirabelle.thy
    Author:     Jasmin Blanchette and Sascha Boehme, TU Munich
*)

theory Mirabelle
imports Main
begin

ML_file \<open>Tools/mirabelle.ML\<close>

ML \<open>Toplevel.add_hook Mirabelle.step_hook\<close>

ML \<open>
signature MIRABELLE_ACTION =
sig
  val invoke : (string * string) list -> theory -> theory
end
\<close>

end
