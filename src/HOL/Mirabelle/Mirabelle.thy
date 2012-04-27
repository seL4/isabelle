(*  Title:      HOL/Mirabelle/Mirabelle.thy
    Author:     Jasmin Blanchette and Sascha Boehme, TU Munich
*)

theory Mirabelle
imports Sledgehammer
uses "Tools/mirabelle.ML"
     "../TPTP/sledgehammer_tactics.ML"
begin

(* no multithreading, no parallel proofs *)  (* FIXME *)
ML {* Multithreading.max_threads := 1 *}
ML {* Goal.parallel_proofs := 0 *}

ML {* Toplevel.add_hook Mirabelle.step_hook *}

ML {*
signature MIRABELLE_ACTION =
sig
  val invoke : (string * string) list -> theory -> theory
end
*}

end
