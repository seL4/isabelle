(*  Title:      Pure/Thy/thy_info.ML
    ID:         $Id$
    Author:     Carsten Clasohm and Markus Wenzel and Sonia Mahjoub and
                Tobias Nipkow and L C Paulson
    Copyright   1994 TU Muenchen

Functions for storing and retrieving arbitrary theory information.
*)

(*Types for theory storage*)

(*Functions to handle arbitrary data added by the user; type "exn" is used
  to store data*)
datatype thy_methods =
  ThyMethods of {merge: exn list -> exn, put: exn -> unit, get: unit -> exn};

datatype thy_info =
  ThyInfo of {path: string,
              children: string list, parents: string list,
              thy_time: string option, ml_time: string option,
              theory: theory option, thms: thm Symtab.table,
              methods: thy_methods Symtab.table,
              data: exn Symtab.table * exn Symtab.table};
      (*thy_time, ml_time = None     theory file has not been read yet
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
  val thyname_of_sign: Sign.sg -> string
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


val loaded_thys =
  ref (Symtab.make [("ProtoPure",
                     ThyInfo {path = "",
                              children = ["Pure", "CPure"], parents = [],
                              thy_time = Some "", ml_time = Some "",
                              theory = Some proto_pure_thy,
                              thms = Symtab.null, methods = Symtab.null,
                              data = (Symtab.null, Symtab.null)}),
                    ("Pure",
                     ThyInfo {path = "", children = [],
                              parents = ["ProtoPure"],
                              thy_time = Some "", ml_time = Some "",
                              theory = Some pure_thy, thms = Symtab.null,
                              methods = Symtab.null,
                              data = (Symtab.null, Symtab.null)}),
                    ("CPure",
                     ThyInfo {path = "",
                              children = [], parents = ["ProtoPure"],
                              thy_time = Some "", ml_time = Some "",
                              theory = Some cpure_thy,
                              thms = Symtab.null,
                              methods = Symtab.null,
                              data = (Symtab.null, Symtab.null)})
                   ]);


(*Get thy_info for a loaded theory *)
fun get_thyinfo tname = Symtab.lookup (!loaded_thys, tname);

(*Get path where theory's files are located*)
fun path_of tname =
  let val ThyInfo {path, ...} = the (get_thyinfo tname)
  in path end;


(*Guess the name of a theory object
  (First the quick way by looking at the stamps; if that doesn't work,
   we search loaded_thys for the first theory which fits.)
*)
fun thyname_of_sign sg =
  let val ref xname = hd (#stamps (Sign.rep_sg sg));
      val opt_info = get_thyinfo xname;

    fun eq_sg (ThyInfo {theory = None, ...}) = false
      | eq_sg (ThyInfo {theory = Some thy, ...}) = Sign.eq_sg (sg,sign_of thy);

    val show_sg = Pretty.str_of o Sign.pretty_sg;
  in
    if is_some opt_info andalso eq_sg (the opt_info) then xname
    else
      (case Symtab.find_first (eq_sg o snd) (!loaded_thys) of
        Some (name, _) => name
      | None => error ("Theory " ^ show_sg sg ^ " not stored by loader"))
  end;


(*Guess to which theory a signature belongs and return it's thy_info*)
fun thyinfo_of_sign sg =
  let val name = thyname_of_sign sg;
  in (name, the (get_thyinfo name)) end;


(*Try to get the theory object corresponding to a given signature*)
fun theory_of_sign sg =
  (case thyinfo_of_sign sg of
    (_, ThyInfo {theory = Some thy, ...}) => thy
  | _ => sys_error "theory_of_sign");


(*Try to get the theory object corresponding to a given theorem*)
val theory_of_thm = theory_of_sign o #sign o rep_thm;


(*Get all direct descendants of a theory*)
fun children_of t =
  case get_thyinfo t of Some (ThyInfo {children, ...}) => children
                      | None => [];


(*Get all direct ancestors of a theory*)
fun parents_of_name t =
  case get_thyinfo t of Some (ThyInfo {parents, ...}) => parents
                      | None => [];


(*Get theory object for a loaded theory *)
fun theory_of name =
  case get_thyinfo name of Some (ThyInfo {theory = Some t, ...}) => t
                         | _ => error ("Theory " ^ name ^
                                       " not stored by loader");


(*Invoke every put method stored in a theory's methods table to initialize
  the state of user defined variables*)
fun put_thydata first tname =
  let val (methods, data) = 
        case get_thyinfo tname of
            Some (ThyInfo {methods, data, ...}) => 
              (methods, Symtab.dest ((if first then fst else snd) data))
          | None => error ("Theory " ^ tname ^ " not stored by loader");

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
               Some (ThyInfo {path, children, parents, thy_time, ml_time, thms,
                              methods, data, ...}) =>
                 ThyInfo {path = path, children = children, parents = parents,
                          thy_time = thy_time, ml_time = ml_time,
                          theory = Some thy, thms = thms,
                          methods = methods, data = data}
             | None => error ("store_theory: theory " ^ tname ^ " not found");
  in loaded_thys := Symtab.update ((tname, tinfo), !loaded_thys) end;


(*** Misc functions ***)

(*Add data handling methods to theory*)
fun add_thydata tname (new_methods as (id, ThyMethods {get, ...})) =
  let val ThyInfo {path, children, parents, thy_time, ml_time, theory,
                   thms, methods, data} =
        case get_thyinfo tname of
            Some ti => ti
          | None => error ("Theory " ^ tname ^ " not stored by loader");
  in loaded_thys := Symtab.update ((tname, ThyInfo {path = path,
       children = children, parents = parents, thy_time = thy_time,
       ml_time = ml_time, theory = theory, thms = thms,
       methods = Symtab.update (new_methods, methods), data = data}),
       !loaded_thys)
  end;


(*Retrieve data associated with theory*)
fun get_thydata tname id =
  let val d2 = case get_thyinfo tname of
                   Some (ThyInfo {data, ...}) => snd data
                 | None => error ("Theory " ^ tname ^ " not stored by loader");
  in Symtab.lookup (d2, id) end;

end;
