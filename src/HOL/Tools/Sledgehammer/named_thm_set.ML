(*  Title:      HOL/Tools/Sledgehammer/named_thm_set.ML
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Named sets of theorems.
*)

signature NAMED_THM_SET =
sig
  val member: Proof.context -> thm -> bool
  val add_thm: thm -> Context.generic -> Context.generic
  val del_thm: thm -> Context.generic -> Context.generic
  val add: attribute
  val del: attribute
  val setup: theory -> theory
end;

functor Named_Thm_Set(val name: string val description: string)
        : NAMED_THM_SET =
struct

structure Data = Generic_Data
(
  type T = thm Termtab.table;
  val empty = Termtab.empty;
  val extend = I;
  fun merge tabs = Termtab.merge (K true) tabs;
);

fun member ctxt th =
  Termtab.defined (Data.get (Context.Proof ctxt)) (Thm.full_prop_of th);

fun add_thm th = Data.map (Termtab.update (Thm.full_prop_of th, th));
fun del_thm th = Data.map (Termtab.delete_safe (Thm.full_prop_of th));

val add = Thm.declaration_attribute add_thm;
val del = Thm.declaration_attribute del_thm;

val setup =
  Attrib.setup (Binding.name name) (Attrib.add_del add del)
               ("declaration of " ^ description) #>
  PureThy.add_thms_dynamic (Binding.name name,
                            map #2 o Termtab.dest o Data.get);

end;
