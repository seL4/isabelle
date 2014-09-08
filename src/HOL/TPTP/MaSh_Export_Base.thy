(*  Title:      HOL/TPTP/MaSh_Export_Base.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* MaSh Exporter Base *}

theory MaSh_Export_Base
imports Main
begin

ML_file "mash_export.ML"

sledgehammer_params
  [provers = spass, max_facts = 32, strict, dont_slice, type_enc = mono_native,
   lam_trans = lifting, timeout = 2, dont_preplay, minimize]

declare [[sledgehammer_fact_duplicates = true]]
declare [[sledgehammer_instantiate_inducts = false]]

hide_fact (open) HOL.ext

ML {*
Multithreading.max_threads_value ()
*}

ML {*
open MaSh_Export
*}

ML {*
val do_it = false (* switch to "true" to generate the files *)
val thys = [@{theory List}]
val params as {provers, ...} = Sledgehammer_Commands.default_params @{theory} []
val prover = hd provers
val range = (1, NONE)
val step = 1
val max_suggestions = 1024
val dir = "List"
val prefix = "/tmp/" ^ dir ^ "/"
*}

end
