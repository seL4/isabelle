(*  Title:      Pure/Thy/thy_info.ML
    ID:         $Id$
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen

Theory loader info database.
*)

(* FIXME wipe out! *)
(*Functions to handle arbitrary data added by the user; type "exn" is used
  to store data*)
datatype thy_methods =
  ThyMethods of {merge: exn list -> exn, put: exn -> unit, get: unit -> exn};


type thy_info =
  {path: string,
    children: string list, parents: string list,
    thy_time: string option, ml_time: string option,
    theory: theory option, thms: thm Symtab.table,
    methods: thy_methods Symtab.table,
    data: exn Symtab.table * exn Symtab.table};

(*
        path: directory where theory's files are located

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

        methods: three methods for each user defined data;
                 merge: merges data of ancestor theories
                 put: retrieves data from loaded_thys and stores it somewhere
                 get: retrieves data from somewhere and stores it
                      in loaded_thys
        data: user defined data; exn is used to allow arbitrary types;
              first element of pairs contains result that get returned after
              thy file was read, second element after ML file was read;
              if ML files has not been read, second element is identical to
              first one because get_thydata, which is meant to return the
              latest data, always accesses the 2nd element
*)

signature THY_INFO =
sig
  val loaded_thys    : thy_info Symtab.table ref
  val store_theory   : theory * string -> unit

  val theory_of      : string -> theory
  val theory_of_sign : Sign.sg -> theory
  val theory_of_thm  : thm -> theory
  val children_of    : string -> string list
  val parents_of_name: string -> string list
  val thyinfo_of_sign: Sign.sg -> string * thy_info

  val add_thydata    : string -> string * thy_methods -> unit
  val get_thydata    : string -> string -> exn option
  val put_thydata    : bool -> string -> unit
  val set_current_thy: string -> unit
  val get_thyinfo    : string -> thy_info option

  val path_of        : string -> string
end;


structure ThyInfo: THY_INFO =
struct

(* loaded theories *)

fun mk_info (name, children, parents, theory) =
  (name,
    {path = "", children = children, parents = parents, thy_time = Some "",
      ml_time = Some "", theory = Some theory, thms = Symtab.null,
      methods = Symtab.null, data = (Symtab.null, Symtab.null)}: thy_info);

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
    Some ({children, ...}) => children
  | None => []);

(*get all direct ancestors of a theory*)
fun parents_of_name t =
  (case get_thyinfo t of
    Some ({parents, ...}) => parents
  | None => []);

(*get theory object for a loaded theory*)
fun theory_of name =
  (case get_thyinfo name of
    Some ({theory = Some t, ...}) => t
  | _ => err_not_stored name);


(*invoke every put method stored in a theory's methods table to initialize
  the state of user defined variables*)
fun put_thydata first tname =
  let val (methods, data) = 
        case get_thyinfo tname of
            Some ({methods, data, ...}) =>
              (methods, Symtab.dest ((if first then fst else snd) data))
          | None => err_not_stored tname;

      fun put_data (id, date) =
            case Symtab.lookup (methods, id) of
                Some (ThyMethods {put, ...}) => put date
              | None => error ("No method defined for theory data \"" ^
                               id ^ "\"");
  in seq put_data data end;


val set_current_thy = put_thydata false;


(*Change theory object for an existent item of loaded_thys*)
fun store_theory (thy, tname) =
  let val tinfo = case Symtab.lookup (!loaded_thys, tname) of
               Some ({path, children, parents, thy_time, ml_time, thms,
                              methods, data, ...}) =>
                 {path = path, children = children, parents = parents,
                          thy_time = thy_time, ml_time = ml_time,
                          theory = Some thy, thms = thms,
                          methods = methods, data = data}
             | None => error ("store_theory: theory " ^ tname ^ " not found");
  in loaded_thys := Symtab.update ((tname, tinfo), !loaded_thys) end;


(*** Misc functions ***)

(*Add data handling methods to theory*)
fun add_thydata tname (new_methods as (id, ThyMethods {get, ...})) =
  let val {path, children, parents, thy_time, ml_time, theory,
                   thms, methods, data} = the_thyinfo tname;
  in loaded_thys := Symtab.update ((tname, {path = path,
       children = children, parents = parents, thy_time = thy_time,
       ml_time = ml_time, theory = theory, thms = thms,
       methods = Symtab.update (new_methods, methods), data = data}),
       !loaded_thys)
  end;


(*retrieve data associated with theory*)
fun get_thydata name id =
  Symtab.lookup (snd (#data (the_thyinfo name)), id);


end;
