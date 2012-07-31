(*  Title:      HOL/Codegenerator_Test/RBT_Set_Test.thy
    Author:     Ondrej Kuncar
*)

header {* Test of the code generator using an implementation of sets by RBT trees *}

theory RBT_Set_Test
imports Library "~~/src/HOL/Library/RBT_Set"
begin

(* 
   The following code equations have to be deleted because they use 
   lists to implement sets in the code generetor. 
*)

lemma [code, code del]:
  "Sup_pred_inst.Sup_pred = Sup_pred_inst.Sup_pred" ..

lemma [code, code del]:
  "Inf_pred_inst.Inf_pred = Inf_pred_inst.Inf_pred" ..

lemma [code, code del]:
  "pred_of_set = pred_of_set" ..


lemma [code, code del]:
  "Cardinality.card' = Cardinality.card'" ..

lemma [code, code del]:
  "Cardinality.finite' = Cardinality.finite'" ..

lemma [code, code del]:
  "Cardinality.subset' = Cardinality.subset'" ..

lemma [code, code del]:
  "Cardinality.eq_set = Cardinality.eq_set" ..


lemma [code, code del]:
  "acc = acc" ..

(*
  If the code generation ends with an exception with the following message:
  '"List.set" is not a constructor, on left hand side of equation: ...',
  the code equation in question has to be either deleted (like many others in this file) 
  or implemented for RBT trees.
*)

export_code _ checking SML OCaml? Haskell? Scala?

end
