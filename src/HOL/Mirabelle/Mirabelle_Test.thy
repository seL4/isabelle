(* Title: Mirabelle_Test.thy
   Author: Sascha Boehme
*)

header {* Simple test theory for Mirabelle actions *}

theory Mirabelle_Test
imports Main Mirabelle
uses
  "Tools/mirabelle_arith.ML"
  "Tools/mirabelle_metis.ML"
  "Tools/mirabelle_quickcheck.ML"
  "Tools/mirabelle_refute.ML"
  "Tools/mirabelle_sledgehammer.ML"
begin

(*
  only perform type-checking of the actions,
  any reasonable test would be too complicated
*)

end
