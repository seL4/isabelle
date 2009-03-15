(*  Title:      HOL/Library/reflection_data.ML
    Author:     Amine Chaieb, TU Muenchen

Data for the reification and reflection methods.
*)

signature REIFY_DATA =
sig
  val get: Proof.context -> thm list * thm list
  val add: attribute
  val del: attribute
  val radd: attribute
  val rdel: attribute
  val setup: theory -> theory
end;

structure Reify_Data : REIFY_DATA =
struct

structure Data = GenericDataFun
(
  type T = thm list * thm list;
  val empty = ([], []);
  val extend = I;
  fun merge _ = pairself Thm.merge_thms;
);

val get = Data.get o Context.Proof;

val add = Thm.declaration_attribute (Data.map o apfst o Thm.add_thm);
val del = Thm.declaration_attribute (Data.map o apfst o Thm.del_thm);
val radd = Thm.declaration_attribute (Data.map o apsnd o Thm.add_thm);
val rdel = Thm.declaration_attribute (Data.map o apsnd o Thm.del_thm);

val setup =
  Attrib.setup @{binding reify} (Attrib.add_del add del) "reify data" #>
  Attrib.setup @{binding reflection} (Attrib.add_del radd rdel) "reflection data";

end;
