(*  Title:      Pure/Thy/thy_info.ML
    ID:         $Id$
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen

Theory loader database.
*)

type thy_info =
  {path: string,
    children: string list, parents: string list,
    thy_time: string option, ml_time: string option,
    theory: theory option};

(*
  path: directory where theory's files are located
	(* FIXME do not store absolute path!!! *)

  thy_time, ml_time = None     theory file has not been read yet
                    = Some ""  theory was read but has either been marked
                               as outdated or there is no such file for
                               this theory (see e.g. 'virtual' theories
                               like Pure or theories without a ML file)
  theory = None  theory has not been read yet

  parents: While 'children' contains all theories the theory depends
           on (i.e. also ones quoted in the .thy file),
           'parents' only contains the theories which were used to form
           the base of this theory.
*)

signature THY_INFO =
sig
  val loaded_thys: thy_info Symtab.table ref
  val get_thyinfo: string -> thy_info option
  val store_theory: theory * string -> unit
  val path_of: string -> string
  val children_of: string -> string list
  val parents_of_name: string -> string list
  val thyinfo_of_sign: Sign.sg -> string * thy_info
  val theory_of: string -> theory
  val theory_of_sign: Sign.sg -> theory
  val theory_of_thm: thm -> theory
end;


structure ThyInfo: THY_INFO =
struct

(* loaded theories *)

fun mk_info (name, children, parents, theory) =
  (name, {path = "", children = children, parents = parents,
    thy_time = Some "", ml_time = Some "", theory = Some theory}: thy_info);

(*preloaded theories*)
val loaded_thys =
  ref (Symtab.make (map mk_info
    [("ProtoPure", ["Pure", "CPure"], [], ProtoPure.thy),
     ("Pure", [], ["ProtoPure"], Pure.thy),
     ("CPure", [], ["ProtoPure"], CPure.thy)]));


(* retrieve info *)

fun err_not_stored name =
  error ("Theory " ^ name ^ " not stored by loader");

fun get_thyinfo name = Symtab.lookup (! loaded_thys, name);

fun the_thyinfo name =
  (case get_thyinfo name of
    Some info => info
  | None => err_not_stored name);

fun thyinfo_of_sign sg =
  let val name = Sign.name_of sg
  in (name, the_thyinfo name) end;


(*path where theory's files are located*)
val path_of = #path o the_thyinfo;


(*try to get the theory object corresponding to a given signature*)
fun theory_of_sign sg =
  (case thyinfo_of_sign sg of
    (_, {theory = Some thy, ...}) => thy
  | _ => sys_error "theory_of_sign");

(*try to get the theory object corresponding to a given theorem*)
val theory_of_thm = theory_of_sign o #sign o rep_thm;

(*get all direct descendants of a theory*)
fun children_of t =
  (case get_thyinfo t of
    Some {children, ...} => children
  | None => []);

(*get all direct ancestors of a theory*)
fun parents_of_name t =
  (case get_thyinfo t of
    Some {parents, ...} => parents
  | None => []);

(*get theory object for a loaded theory*)
fun theory_of name =
  (case get_thyinfo name of
    Some {theory = Some t, ...} => t
  | _ => err_not_stored name);


(* store_theory *)

fun store_theory (thy, name) =
  let
    val {path, children, parents, thy_time, ml_time, theory = _} =
      the_thyinfo name;
    val info = {path = path, children = children, parents = parents,
      thy_time = thy_time, ml_time = ml_time, theory = Some thy};
  in
    loaded_thys := Symtab.update ((name, info), ! loaded_thys)
  end;


end;
