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
  val datatypesK: string;
  val get_record_data: theory -> ((string * (string * ctyp) list) Symtab.table);
  val put_record_data: ((string * (string * ctyp) list) Symtab.table) -> theory -> theory;
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
  (* get and put datatypes *)

  fun get_datatypes_sg sg =
    (case Sign.get_data sg datatypesK of
      DatatypeInfo tab => tab
    | _ => sys_error "get_datatypes_sg");

  val get_datatypes = get_datatypes_sg o sign_of;

  fun put_datatypes tab thy =
    Theory.put_data (datatypesK, DatatypeInfo tab) thy;
end;


(** records **)

(* data kind 'records' *)

(* methods *)

local

  val recordsK = "records";
  exception Records of
    (string * (string * ctyp) list) Symtab.table;

  fun forget_Records (Records t) = t; (* FIXME *) (* not very nice *)

  val empty = Records Symtab.null;

  fun prep_ext r = r;

  fun merge (Records rs1, Records rs2) = Records (Symtab.merge (fn (a,b) => true) (rs1, rs2));

  fun print_aux (record_name, (parent, (sels_types))) = 
     let val sel_types_string = 
             (map (fn (sel,sel_type) => Pretty.block([Pretty.str (sel ^ " :: "), 
                                                    Pretty.quote (Pretty.str (Display.string_of_ctyp sel_type))])));
      in
      Pretty.big_list ("record " ^ record_name ^ " =")
                      (if parent = "" then (sel_types_string sels_types)
                                      else (Pretty.str (parent ^ " +")) :: (sel_types_string sels_types))
      end;

  fun print (Records rs) =
      if (Symtab.is_null rs) then
        Pretty.writeln (Pretty.str ("no records available")) else
        let val data = (Symtab.dest rs) in
           seq Pretty.writeln (map print_aux data)
        end;
  in

  val record_thy_data = (recordsK, (empty, prep_ext, merge, print));
  fun get_record_data thy  = forget_Records(Theory.get_data thy recordsK);
  fun put_record_data rd = Theory.put_data (recordsK, Records rd);

  end;


(** hol_data **)

val hol_data =
 [Simplifier.simpset_thy_data, ClasetThyData.thy_data, datatypes_thy_data, record_thy_data];

end;
