(* Title: Mirabelle.thy
   Author: Jasmin Blanchette and Sascha Boehme
*)

theory Mirabelle
imports Pure
uses "Tools/mirabelle.ML"
begin

(* no multithreading, no parallel proofs *)
ML {* Multithreading.max_threads := 1 *}
ML {* Goal.parallel_proofs := 0 *}

ML {* Toplevel.add_hook Mirabelle.step_hook *}

setup Mirabelle.setup

ML {*
signature MIRABELLE_ACTION =
sig
  val invoke : (string * string) list -> theory -> theory
end
*}

end
