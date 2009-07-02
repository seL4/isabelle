(*  Title:      Pure/Tools/named_thms.ML
    Author:     Makarius

Named collections of theorems in canonical order.
*)

signature NAMED_THMS =
sig
  val get: Proof.context -> thm list
  val add_thm: thm -> Context.generic -> Context.generic
  val del_thm: thm -> Context.generic -> Context.generic
  val add: attribute
  val del: attribute
  val setup: theory -> theory
end;

functor Named_Thms(val name: string val description: string): NAMED_THMS =
struct

structure Data = GenericDataFun
(
  type T = thm list;
  val empty = [];
  val extend = I;
  fun merge _ = Thm.merge_thms;
);

val get = Data.get o Context.Proof;

val add_thm = Data.map o Thm.add_thm;
val del_thm = Data.map o Thm.del_thm;

val add = Thm.declaration_attribute add_thm;
val del = Thm.declaration_attribute del_thm;

val setup =
  Attrib.setup (Binding.name name) (Attrib.add_del add del) ("declaration of " ^ description) #>
  PureThy.add_thms_dynamic (Binding.name name, Data.get);

end;
