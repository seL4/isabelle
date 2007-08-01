(*  Title:      Pure/Tools/named_thms.ML
    ID:         $Id$
    Author:     Makarius

Named collections of theorems in canonical order.
*)

signature NAMED_THMS =
sig
  val get: Proof.context -> thm list
  val pretty: Proof.context -> Pretty.T
  val add: attribute
  val del: attribute
  val setup: theory -> theory
end;

functor NamedThmsFun(val name: string val description: string): NAMED_THMS =
struct

structure Data = GenericDataFun
(
  type T = thm list;
  val empty = [];
  val extend = I;
  fun merge _ = Thm.merge_thms;
);

val get = Data.get o Context.Proof;

fun pretty ctxt =
  Pretty.big_list (description ^ ":") (map (ProofContext.pretty_thm ctxt) (get ctxt));

val add = Thm.declaration_attribute (Data.map o Thm.add_thm);
val del = Thm.declaration_attribute (Data.map o Thm.del_thm);

val setup =
  Attrib.add_attributes [(name, Attrib.add_del_args add del, "declaration of " ^ description)];

val _ = OuterSyntax.add_parsers
 [OuterSyntax.improper_command ("print_" ^ name ^ "_rules") ("print " ^ description)
    OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o
      Toplevel.keep (Pretty.writeln o pretty o Toplevel.context_of)))];

end;
