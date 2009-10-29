(*  Title:      HOL/Tools/res_blacklist.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Makarius

Theorems blacklisted to sledgehammer.  These theorems typically
produce clauses that are prolific (match too many equality or
membership literals) and relate to seldom-used facts.  Some duplicate
other rules.
*)

signature RES_BLACKLIST =
sig
  val setup: theory -> theory
  val blacklisted: Proof.context -> thm -> bool
  val add: attribute
  val del: attribute
end;

structure Res_Blacklist: RES_BLACKLIST =
struct

structure Data = GenericDataFun
(
  type T = thm Termtab.table;
  val empty = Termtab.empty;
  val extend = I;
  fun merge _ tabs = Termtab.merge (K true) tabs;
);

fun blacklisted ctxt th =
  Termtab.defined (Data.get (Context.Proof ctxt)) (Thm.full_prop_of th);

fun add_thm th = Data.map (Termtab.update (Thm.full_prop_of th, th));
fun del_thm th = Data.map (Termtab.delete_safe (Thm.full_prop_of th));

val add = Thm.declaration_attribute add_thm;
val del = Thm.declaration_attribute del_thm;

val setup =
  Attrib.setup @{binding noatp} (Attrib.add_del add del) "sledgehammer blacklisting" #>
  PureThy.add_thms_dynamic (@{binding noatp}, map #2 o Termtab.dest o Data.get);

end;
