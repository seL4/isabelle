(*  Title:      HOL/Mirabelle/Mirabelle.thy
    Author:     Jasmin Blanchette and Sascha Boehme, TU Munich
*)

theory Mirabelle
imports Sledgehammer
begin

ML_file "Tools/mirabelle.ML"
ML_file "../TPTP/sledgehammer_tactics.ML"

ML {* Toplevel.add_hook Mirabelle.step_hook *}

ML {*
signature MIRABELLE_ACTION =
sig
  val invoke : (string * string) list -> theory -> theory
end
*}

end
