(*  Title:      HOL/thy_data.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

HOL theory data: datatypes.
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
  val setup: (theory -> theory) list
end;

structure ThyData: THY_DATA =
struct


(* data kind 'datatypes' *)

local
  val datatypesK = Object.kind "HOL/datatypes";
  exception DatatypeInfo of datatype_info Symtab.table;

  val empty = DatatypeInfo Symtab.empty;

  fun prep_ext (x as DatatypeInfo _) = x;

  fun merge (DatatypeInfo tab1, DatatypeInfo tab2) =
    DatatypeInfo (Symtab.merge (K true) (tab1, tab2));

  fun print sg (DatatypeInfo tab) =
    Pretty.writeln (Pretty.strs ("datatypes:" ::
      map (Sign.cond_extern sg Sign.typeK o fst) (Symtab.dest tab)));
in
  val init_datatypes = Theory.init_data datatypesK (empty, prep_ext, merge, print);
  val get_datatypes_sg = Sign.get_data datatypesK (fn DatatypeInfo tab => tab);
  val get_datatypes = get_datatypes_sg o sign_of;
  val put_datatypes = Theory.put_data datatypesK DatatypeInfo;
end;


(* setup *)

val setup = [init_datatypes];


end;
