(*  ID:         $Id$
    Author:     Jia Meng, NICTA

ATP rules.
*)

signature RES_ATPSET =
sig
  val print_atpset: Proof.context -> unit
  val get_atpset: Proof.context -> thm list
  val atp_add: attribute
  val atp_del: attribute
  val setup: theory -> theory
end;

structure ResAtpset: RES_ATPSET =
struct

structure Data = GenericDataFun
(
  val name = "HOL/atpset";
  type T = thm list;
  val empty = [];
  val extend = I;
  fun merge _ = Drule.merge_rules;
  fun print context rules =
    Pretty.writeln (Pretty.big_list "ATP rules:"
      (map (ProofContext.pretty_thm (Context.proof_of context)) rules));
);

val print_atpset = Data.print o Context.Proof;
val get_atpset = Data.get o Context.Proof;

val atp_add = Thm.declaration_attribute (Data.map o Drule.add_rule);
val atp_del = Thm.declaration_attribute (Data.map o Drule.del_rule);

val setup =
  Data.init #>
  Attrib.add_attributes [("atp", Attrib.add_del_args atp_add atp_del, "declaration of ATP rules")];

end;
