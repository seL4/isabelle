(*  Title:      HOL/Mirabelle/Mirabelle_Test.thy
    Author:     Sascha Boehme, TU Munich
*)

header {* Simple test theory for Mirabelle actions *}

theory Mirabelle_Test
imports Main Mirabelle
uses
  "Actions/mirabelle_arith.ML"
  "Actions/mirabelle_metis.ML"
  "Actions/mirabelle_quickcheck.ML"
  "Actions/mirabelle_refute.ML"
  "Actions/mirabelle_sledgehammer.ML"
  "Actions/mirabelle_sledgehammer_filter.ML"
begin

text {*
  Only perform type-checking of the actions,
  any reasonable test would be too complicated.
*}

end
