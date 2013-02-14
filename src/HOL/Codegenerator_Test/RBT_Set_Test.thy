(*  Title:      HOL/Codegenerator_Test/RBT_Set_Test.thy
    Author:     Ondrej Kuncar
*)

header {* Test of the code generator using an implementation of sets by RBT trees *}

theory RBT_Set_Test
imports "~~/src/HOL/Library/Library" "~~/src/HOL/Library/RBT_Set"
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
  "acc = acc" ..

lemmas [code del] =
  finite_set_code finite_coset_code 
  equal_set_code

(*
  If the code generation ends with an exception with the following message:
  '"List.set" is not a constructor, on left hand side of equation: ...',
  the code equation in question has to be either deleted (like many others in this file) 
  or implemented for RBT trees.
*)

export_code _ checking SML OCaml? Haskell?

(* Extra setup to make Scala happy *)
(* If the compilation fails with an error "ambiguous implicit values",
   read \<section>7.1 in the Code Generation Manual *)

class ccpo_linorder = ccpo + linorder

lemma [code]:
  "(Complete_Partial_Order.admissible :: ('a :: ccpo_linorder \<Rightarrow> bool) \<Rightarrow> bool) P = 
    (\<forall>A. Complete_Partial_Order.chain (op \<le>) A \<longrightarrow> (\<forall>x\<in>A. P x) \<longrightarrow> P (Sup A))"
unfolding admissible_def by blast

lemma [code]:
  "(gfp :: ('a :: complete_linorder \<Rightarrow> 'a) \<Rightarrow> 'a) f = Sup {u. u \<le> f u}"
unfolding gfp_def by blast

lemma [code]:
  "(lfp :: ('a :: complete_linorder \<Rightarrow> 'a) \<Rightarrow> 'a) f = Inf {u. f u \<le> u}"
unfolding lfp_def by blast

export_code _ checking Scala?

end
