(*  Title:      HOL/thy_data.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

HOL theory data: simpset, claset, records, datatypes.
*)

(*for records*)
type record_info =
 {parent: string option,
  fields: (string * typ) list};

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
  val get_records: theory -> record_info Symtab.table;
  val put_records: record_info Symtab.table -> theory -> theory;
  val get_datatypes_sg: Sign.sg -> datatype_info Symtab.table
  val get_datatypes: theory -> datatype_info Symtab.table
  val put_datatypes: datatype_info Symtab.table -> theory -> theory
  val hol_data: (string * (object * (object -> object) *
    (object * object -> object) * (Sign.sg -> object -> unit))) list
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
  | _ => sys_error "get_datatypes_sg");

val get_datatypes = get_datatypes_sg o sign_of;

fun put_datatypes tab thy =
  Theory.put_data (datatypesK, DatatypeInfo tab) thy;



(** records **)

(* data kind 'records' *)

val recordsK = "records";
exception Records of record_info Symtab.table;


(* methods *)

local
  val empty = Records Symtab.null;

  fun prep_ext (x as Records _) = x;

  fun merge (Records tab1, Records tab2) =
    Records (Symtab.merge (K true) (tab1, tab2));

  fun print sg (Records tab) =
    let
      fun pretty_parent None = []
        | pretty_parent (Some name) =
            [Pretty.str (Sign.cond_extern sg Sign.typeK name ^ " +")];

      fun pretty_field (c, T) = Pretty.block
        [Pretty.str (Sign.cond_extern sg Sign.constK c ^ " :: "),
          Pretty.brk 1, Pretty.quote (Sign.pretty_typ sg T)];

      fun pretty_record (name, {parent, fields}) =
        Pretty.big_list (name ^ " =") (pretty_parent parent @ map pretty_field fields);
    in
      seq (Pretty.writeln o pretty_record) (Symtab.dest tab)
    end;
in
  val record_thy_data = (recordsK, (empty, prep_ext, merge, print));
end;


(* get and put records *)

fun get_records thy =
  (case Theory.get_data thy recordsK of
    Records tab => tab
  | _ => sys_error "get_records");

fun put_records tab thy =
  Theory.put_data (recordsK, Records tab) thy;



(** hol_data **)

val hol_data =
 [Simplifier.simpset_thy_data,
  ClasetThyData.thy_data,
  datatypes_thy_data,
  record_thy_data];


end;
