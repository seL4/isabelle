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


(* data kind 'HOL/datatypes' *)

structure DatatypesArgs =
struct
  val name = "HOL/datatypes";
  type T = datatype_info Symtab.table;

  val empty = Symtab.empty;
  val prep_ext = I;
  val merge: T * T -> T = Symtab.merge (K true);

  fun print sg tab =
    Pretty.writeln (Pretty.strs ("datatypes:" ::
      map (Sign.cond_extern sg Sign.typeK o fst) (Symtab.dest tab)));
end;

structure DatatypesData = TheoryDataFun(DatatypesArgs);
val get_datatypes_sg = DatatypesData.get_sg;
val get_datatypes = DatatypesData.get;
val put_datatypes = DatatypesData.put;


(* setup *)

val setup = [DatatypesData.init];


end;
