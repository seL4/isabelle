(*  Title:      HOL/thy_data.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

HOL theory data.
*)

type datatype_info =
 {case_const: term,
  case_rewrites: thm list,
  constructors: term list,
  induct_tac: string -> int -> tactic,
  nchotomy: thm,
  exhaustion: thm,
  exhaust_tac: string -> int -> tactic,
  case_cong: thm};

signature THY_DATA =
sig
  val datatypesK: string
  val hol_data: (string * (exn * (exn -> exn) * (exn * exn -> exn) * (exn -> unit))) list
end;

structure ThyData: THY_DATA =
struct


(** datatypes **)	(* FIXME *)

val datatypesK = "datatypes";
exception DatatypeInfo of datatype_info Symtab.table;



(** records **)		(* FIXME *)

val recordsK = "records";



(** hol_data **)

val hol_data =
 [Simplifier.simpset_thy_data, ClasetThyData.thy_data];


end;
