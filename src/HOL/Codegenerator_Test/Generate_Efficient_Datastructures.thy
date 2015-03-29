
(* Author: Ondrej Kuncar, TU Muenchen *)

section {* Pervasive test of code generator *}

theory Generate_Efficient_Datastructures
imports
  Candidates
  "~~/src/HOL/Library/DAList_Multiset"
  "~~/src/HOL/Library/RBT_Mapping"
  "~~/src/HOL/Library/RBT_Set"
begin

setup \<open>
fn thy =>
let
  val tycos = Sign.logical_types thy;
  val consts = map_filter (try (curry (Axclass.param_of_inst thy)
    @{const_name "Quickcheck_Narrowing.partial_term_of"})) tycos;
in fold Code.del_eqns consts thy end
\<close> -- \<open>drop technical stuff from @{text Quickcheck_Narrowing} which is tailored towards Haskell\<close>

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
  "Wellfounded.acc = Wellfounded.acc" ..

lemma [code, code del]:
  "Cardinality.card' = Cardinality.card'" ..

lemma [code, code del]:
  "Cardinality.finite' = Cardinality.finite'" ..

lemma [code, code del]:
  "Cardinality.subset' = Cardinality.subset'" ..

lemma [code, code del]:
  "Cardinality.eq_set = Cardinality.eq_set" ..

lemma [code, code del]:
  "(Gcd :: nat set \<Rightarrow> nat) = Gcd" ..

lemma [code, code del]:
  "(Lcm :: nat set \<Rightarrow> nat) = Lcm" ..

lemma [code, code del]:
  "(Gcd :: int set \<Rightarrow> int) = Gcd" ..

lemma [code, code del]:
  "(Lcm :: int set \<Rightarrow> int) = Lcm" ..
  
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

lemma [code]:
  "(gfp :: ('a :: complete_linorder \<Rightarrow> 'a) \<Rightarrow> 'a) f = Sup {u. u \<le> f u}"
unfolding gfp_def by blast

lemma [code]:
  "(lfp :: ('a :: complete_linorder \<Rightarrow> 'a) \<Rightarrow> 'a) f = Inf {u. f u \<le> u}"
unfolding lfp_def by blast

export_code _ checking Scala?

end
