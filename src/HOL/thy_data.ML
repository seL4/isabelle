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
  val get_datatypes_sg: Sign.sg -> datatype_info Symtab.table
  val get_datatypes: theory -> datatype_info Symtab.table
  val put_datatypes: datatype_info Symtab.table -> theory -> theory
  val hol_data: (string * (exn * (exn -> exn) * (exn * exn -> exn) * (exn -> unit))) list
end;

structure ThyData: THY_DATA =
struct


(** datatypes **)

(* data kind 'datatypes' *)

val datatypesK = "datatypes";
exception DatatypeInfo of datatype_info Symtab.table;

local
  val empty = DatatypeInfo Symtab.null;

  fun prep_ext (x as DatatypeInfo _) = x;

  fun merge (DatatypeInfo tab1, DatatypeInfo tab2) =
    DatatypeInfo (Symtab.merge (K true) (tab1, tab2));

  fun print (DatatypeInfo tab) =
    Pretty.writeln (Pretty.strs ("datatypes:" :: map fst (Symtab.dest tab)));
in
  val datatypes_thy_data = (datatypesK, (empty, prep_ext, merge, print));
end;


(* get and put datatypes *)

fun get_datatypes_sg sg =
  (case Sign.get_data sg datatypesK of
    DatatypeInfo tab => tab
  | _ => sys_error "get_datatypes_sg");

val get_datatypes = get_datatypes_sg o sign_of;

fun put_datatypes tab thy =
  Theory.put_data (datatypesK, DatatypeInfo tab) thy;



(** records **)         (* FIXME *)

val recordsK = "records";



(** hol_data **)

val hol_data =
 [Simplifier.simpset_thy_data, ClasetThyData.thy_data, datatypes_thy_data];


end;
