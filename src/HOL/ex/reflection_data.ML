(*  Title:      HOL/ex/reflection_data.ML
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen

Data for the reification and  reflection Methods
*)

signature REIFY_DATA =
sig
  type entry
  val get: Proof.context -> entry
  val del: attribute
  val add: attribute 
  val setup: theory -> theory
end;

structure Reify_Data : REIFY_DATA =
struct

type entry = thm list;

structure Data = GenericDataFun
( val name = "Reify-Data";
  type T = thm list
  val empty = [];
  val extend = I
  fun merge _ = Library.merge Thm.eq_thm);

val get = Data.get o Context.Proof;

val add = Thm.declaration_attribute (fn th => fn context => 
  context |> Data.map (Drule.add_rule th ))

val del = Thm.declaration_attribute (fn th => fn context => 
  context |> Data.map (Drule.del_rule th ))

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
fun att_syntax src = src |> Attrib.syntax
 ((Scan.lift (Args.$$$ "del") |-- thms) >> del ||
  optional (keyword addN |-- thms) >> add)
end;
*)

(* theory setup *)
 val setup =
  Attrib.add_attributes [("reify", Attrib.add_del_args add del, "Reify data")];
end;
