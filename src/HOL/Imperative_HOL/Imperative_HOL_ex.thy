(*  Title:      HOL/Imperative_HOL/Imperative_HOL_ex.thy
    Author:     John Matthews, Galois Connections;
                Alexander Krauss, Lukas Bulwahn & Florian Haftmann, TU Muenchen
*)

section {* Monadic imperative HOL with examples *}

theory Imperative_HOL_ex
imports Imperative_HOL Overview
  "ex/Imperative_Quicksort" "ex/Imperative_Reverse" "ex/Linked_Lists" "ex/SatChecker"
  Legacy_Mrec
begin

definition "everything = (Array.new, Array.of_list, Array.make, Array.len, Array.nth,
  Array.upd, Array.map_entry, Array.swap, Array.freeze,
  ref, Ref.lookup, Ref.update, Ref.change)"

export_code everything checking SML SML_imp OCaml? OCaml_imp? Haskell? Scala Scala_imp

end
