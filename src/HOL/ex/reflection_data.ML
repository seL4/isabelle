(*  Title:      HOL/ex/reflection_data.ML
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen

Data for the reification and reflection methods.
*)

signature REIFY_DATA =
sig
  type entry = thm list * thm list
  val get: Proof.context -> entry
  val del: attribute
  val add: attribute
  val setup: theory -> theory
end;

structure Reify_Data : REIFY_DATA =
struct

type entry = thm list * thm list;

structure Data = GenericDataFun
(
  type T = entry
  val empty = ([], [])
  val extend = I
  fun merge _ = pairself Thm.merge_thms
);

val get = Data.get o Context.Proof;

val add = Thm.declaration_attribute (fn th => fn context =>
  context |> Data.map (apfst (Thm.add_thm th)))

val del = Thm.declaration_attribute (fn th => fn context =>
  context |> Data.map (apfst (Thm.del_thm th)))

val radd = Thm.declaration_attribute (fn th => fn context =>
  context |> Data.map (apsnd (Thm.add_thm th)))

val rdel = Thm.declaration_attribute (fn th => fn context =>
  context |> Data.map (apsnd (Thm.del_thm th)))

(* concrete syntax *)
(*
local
fun keyword k = Scan.lift (Args.$$$ k -- Args.colon) >> K ();

val constsN = "consts";
val addN = "add";
val delN = "del";
val any_keyword = keyword constsN || keyword addN || keyword delN;
val thms = Scan.repeat (Scan.unless any_keyword Attrib.multi_thm) >> flat;
val terms = thms >> map (term_of o Drule.dest_term);

fun optional scan = Scan.optional scan [];

in
val att_syntax = Attrib.syntax
 ((Scan.lift (Args.$$$ "del") |-- thms) >> del ||
  optional (keyword addN |-- thms) >> add)
end;
*)

(* theory setup *)
 val setup =
  Attrib.add_attributes [("reify", Attrib.add_del_args add del, "Reify data"),
                         ("reflection", Attrib.add_del_args radd rdel, "Reflection data")];
end;
