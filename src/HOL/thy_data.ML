(*  Title:      HOL/thy_data.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

HOL theory data: datatypes.
*)

(*for datatypes*)
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
  val setup: (theory -> theory) list
end;

structure ThyData: THY_DATA =
struct


(** datatypes **)

(* data kind 'datatypes' *)

val datatypesK = "HOL/datatypes";
exception DatatypeInfo of datatype_info Symtab.table;

local
  val empty = DatatypeInfo Symtab.empty;

  fun prep_ext (x as DatatypeInfo _) = x;

  fun merge (DatatypeInfo tab1, DatatypeInfo tab2) =
    DatatypeInfo (Symtab.merge (K true) (tab1, tab2));

  fun print sg (DatatypeInfo tab) =
    Pretty.writeln (Pretty.strs ("datatypes:" ::
      map (Sign.cond_extern sg Sign.typeK o fst) (Symtab.dest tab)));
in
  val datatypes_thy_data = (datatypesK, (empty, prep_ext, merge, print));
end;


(* get and put datatypes *)

fun get_datatypes_sg sg =
  (case Sign.get_data sg datatypesK of
    DatatypeInfo tab => tab
  | _ => type_error datatypesK);

val get_datatypes = get_datatypes_sg o sign_of;

fun put_datatypes tab thy =
  Theory.put_data (datatypesK, DatatypeInfo tab) thy;



(** theory data setup **)

val setup = [Theory.init_data [datatypes_thy_data]];


end;
