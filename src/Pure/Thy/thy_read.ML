(*  Title:      Pure/Thy/thy_read.ML
    ID:         $Id$
    Author:     Carsten Clasohm and Markus Wenzel and Sonia Mahjoub and
                Tobias Nipkow and L C Paulson
    Copyright   1994 TU Muenchen

(* FIXME !? *)
Reading and writing the theory definition files.

(* FIXME !? *)
For theory XXX, the  input file is called XXX.thy
                the output file is called .XXX.thy.ML
                and it then tries to read XXX.ML
*)

datatype thy_info = ThyInfo of {path: string,
                                children: string list,
                                thy_time: string option,
                                ml_time: string option,
                                theory: theory option,
                                thms: thm Symtab.table};

signature READTHY =
sig
  datatype basetype = Thy  of string
                    | File of string

  val loaded_thys    : thy_info Symtab.table ref
  val loadpath       : string list ref
  val delete_tmpfiles: bool ref

  val use_thy        : string -> unit
  val update         : unit -> unit
  val time_use_thy   : string -> unit
  val unlink_thy     : string -> unit
  val mk_base        : basetype list -> string -> bool -> theory
  val store_theory   : theory * string -> unit

  val theory_of_sign: Sign.sg -> theory
  val theory_of_thm: thm -> theory
  val store_thm: string * thm -> thm
  val qed: string -> unit
  val get_thm: theory -> string -> thm
  val thms_of: theory -> (string * thm) list
end;


functor ReadthyFUN(structure ThySyn: THY_SYN): READTHY =
struct

datatype basetype = Thy  of string
                  | File of string;

val loaded_thys = ref (Symtab.make [("Pure", ThyInfo {path = "", children = [],
                                       thy_time = Some "", ml_time = Some "",
                                       theory = Some pure_thy,
                                       thms = Symtab.null})]);

val loadpath = ref ["."];           (*default search path for theory files *)

val delete_tmpfiles = ref true;         (*remove temporary files after use *)

(*Make name of the output ML file for a theory *)
fun out_name tname = "." ^ tname ^ ".thy.ML";

(*Read a file specified by thy_file containing theory thy *)
fun read_thy tname thy_file =
  let
    val instream  = open_in thy_file;
    val outstream = open_out (out_name tname);
  in
    output (outstream, ThySyn.parse tname (input (instream, 999999)));
    close_out outstream;
    close_in instream
  end;

fun file_exists file =
  let val instream = open_in file in close_in instream; true end
    handle Io _ => false;

(*Get thy_info for a loaded theory *)
fun get_thyinfo tname = Symtab.lookup (!loaded_thys, tname);

(*Check if a theory was already loaded *)
fun already_loaded thy =
  let val t = get_thyinfo thy
  in if is_none t then false
     else let val ThyInfo {thy_time, ml_time, ...} = the t
          in if is_none thy_time orelse is_none ml_time then false
             else true
          end
  end;

(*Check if a theory file has changed since its last use.
  Return a pair of boolean values for .thy and for .ML *)
fun thy_unchanged thy thy_file ml_file =
  let val t = get_thyinfo thy
  in if is_some t then
       let val ThyInfo {thy_time, ml_time, ...} = the t
           val tn = is_none thy_time;
           val mn = is_none ml_time
       in if not tn andalso not mn then
              ((file_info thy_file = the thy_time),
               (file_info ml_file = the ml_time))
          else if not tn andalso mn then (true, false)
          else (false, false)
       end
     else (false, false)
  end;

exception FILE_NOT_FOUND;   (*raised by find_file *)

(*Find a file using a list of paths if no absolute or relative path is
  specified.*)
fun find_file "" name =
      let fun find_it (curr :: paths) =
                if file_exists (tack_on curr name) then
                    tack_on curr name
                else
                    find_it paths
           | find_it [] = ""
      in find_it (!loadpath) end
  | find_file path name =
      if file_exists (tack_on path name) then tack_on path name
                                         else "";

(*Get absolute pathnames for a new or already loaded theory *)
fun get_filenames path name =
  let fun make_absolute file =
        if file = "" then "" else
            if hd (explode file) = "/" then file else tack_on (pwd ()) file;

      fun new_filename () =
        let val found = find_file path (name ^ ".thy")
                        handle FILE_NOT_FOUND => "";
            val thy_file = make_absolute found;
            val (thy_path, _) = split_filename thy_file;
            val found = find_file path (name ^ ".ML");
            val ml_file = if thy_file = "" then make_absolute found
                          else if file_exists (tack_on thy_path (name ^ ".ML"))
                          then tack_on thy_path (name ^ ".ML")
                          else "";
            val searched_dirs = if path = "" then (!loadpath) else [path]
        in if thy_file = "" andalso ml_file = "" then
             error ("Could not find file \"" ^ name ^ ".thy\" or \""
                    ^ name ^ ".ML\" for theory \"" ^ name ^ "\"\n"
                    ^ "in the following directories: \"" ^
                    (space_implode "\", \"" searched_dirs) ^ "\"")
           else ();
           (thy_file, ml_file)
        end;

      val tinfo = get_thyinfo name;
  in if is_some tinfo andalso path = "" then
       let val ThyInfo {path = abs_path, ...} = the tinfo;
           val (thy_file, ml_file) = if abs_path = "" then new_filename ()
                                     else (find_file abs_path (name ^ ".thy"),
                                           find_file abs_path (name ^ ".ML"))
       in if thy_file = "" andalso ml_file = "" then
            (writeln ("Warning: File \"" ^ (tack_on path name)
                      ^ ".thy\"\ncontaining theory \"" ^ name
                      ^ "\" no longer exists.");
             new_filename ()
            )
          else (thy_file, ml_file)
       end
     else new_filename ()
  end;

(*Remove theory from all child lists in loaded_thys *)
fun unlink_thy tname =
  let fun remove (ThyInfo {path, children, thy_time, ml_time, theory, thms}) =
        ThyInfo {path = path, children = children \ tname,
                 thy_time = thy_time, ml_time = ml_time,
                 theory = theory, thms = thms}
  in loaded_thys := Symtab.map remove (!loaded_thys) end;

(*Remove a theory from loaded_thys *)
fun remove_thy tname =
  loaded_thys := Symtab.make (filter_out (fn (id, _) => id = tname)
                 (Symtab.dest (!loaded_thys)));

(*Change thy_time and ml_time for an existent item *)
fun set_info thy_time ml_time tname =
  let val ThyInfo {path, children, theory, thms, ...} =
        the (Symtab.lookup (!loaded_thys, tname));
  in loaded_thys := Symtab.update ((tname,
       ThyInfo {path = path, children = children,
                thy_time = Some thy_time, ml_time = Some ml_time,
                theory = theory, thms = thms}), !loaded_thys)
  end;

(*Mark theory as changed since last read if it has been completly read *)
fun mark_outdated tname =
  if already_loaded tname then set_info "" "" tname else ();

(*Read .thy and .ML files that haven't been read yet or have changed since
  they were last read;
  loaded_thys is a thy_info list ref containing all theories that have
  completly been read by this and preceeding use_thy calls.
  If a theory changed since its last use its children are marked as changed *)
fun use_thy name =
    let val (path, tname) = split_filename name;
        val (thy_file, ml_file) = get_filenames path tname;
        val (abs_path, _) = if thy_file = "" then split_filename ml_file
                            else split_filename thy_file;
        val (thy_uptodate, ml_uptodate) = thy_unchanged tname
                                                        thy_file ml_file;

         (*Set absolute path for loaded theory *)
         fun set_path () =
           let val ThyInfo {children, thy_time, ml_time, theory, thms, ...} =
                 the (Symtab.lookup (!loaded_thys, tname));
           in loaded_thys := Symtab.update ((tname,
                               ThyInfo {path = abs_path, children = children,
                                        thy_time = thy_time, ml_time = ml_time,
                                        theory = theory, thms = thms}),
                               !loaded_thys)
           end;

         (*Mark all direct descendants of a theory as changed *)
         fun mark_children thy =
           let val ThyInfo {children, ...} = the (get_thyinfo thy)
               val loaded = filter already_loaded children
           in if loaded <> [] then
                  (writeln ("The following children of theory " ^ (quote thy)
                            ^ " are now out-of-date: "
                            ^ (quote (space_implode "\",\"" loaded)));
                   seq mark_outdated loaded
                  )
              else ()
           end;

        (*Remove all theorems associated with a theory*)
        fun delete_thms () =
          let val tinfo = case Symtab.lookup (!loaded_thys, tname) of
             Some (ThyInfo {path, children, thy_time, ml_time, theory, ...}) =>
                 ThyInfo {path = path, children = children,
                          thy_time = thy_time, ml_time = ml_time,
                          theory = theory, thms = Symtab.null}
           | None => ThyInfo {path = "", children = [],
                              thy_time = None, ml_time = None,
                              theory = None, thms = Symtab.null};
         in loaded_thys := Symtab.update ((tname, tinfo), !loaded_thys) end;
    in if thy_uptodate andalso ml_uptodate then ()
       else
       (
         delete_thms ();

         if thy_uptodate orelse thy_file = "" then ()
         else (writeln ("Reading \"" ^ name ^ ".thy\"");
               read_thy tname thy_file;
               use (out_name tname)
              );

         if ml_file = "" then ()
         else (writeln ("Reading \"" ^ name ^ ".ML\"");
               use ml_file);

         use_string ["store_theory (" ^ tname ^ ".thy, " ^ quote tname ^ ");"];

         (*Now set the correct info*)
         set_info (file_info thy_file) (file_info ml_file) tname;
         set_path ();

         (*Mark theories that have to be reloaded*)
         mark_children tname;

         (*Remove temporary files*)
         if not (!delete_tmpfiles) orelse (thy_file = "") orelse thy_uptodate
           then ()
         else delete_file (out_name tname)
        )
    end;

fun time_use_thy tname = timeit(fn()=>
   (writeln("\n**** Starting Theory " ^ tname ^ " ****");
    use_thy tname;
    writeln("\n**** Finished Theory " ^ tname ^ " ****"))
   );

(*Load all thy or ML files that have been changed and also
  all theories that depend on them *)
fun update () =
  let (*List theories in the order they have to be loaded *)
      fun load_order [] result = result
        | load_order thys result =
            let fun next_level (t :: ts) =
                      let val thy = get_thyinfo t
                      in if is_some thy then
                             let val ThyInfo {children, ...} = the thy
                             in children union (next_level ts) end
                         else next_level ts
                      end
                  | next_level [] = [];

                val children = next_level thys;
            in load_order children ((result \\ children) @ children) end;

      fun reload_changed (t :: ts) =
            let val thy = get_thyinfo t;

                fun abspath () =
                  if is_some thy then
                    let val ThyInfo {path, ...} = the thy in path end
                  else "";

                val (thy_file, ml_file) = get_filenames (abspath ()) t;
                val (thy_uptodate, ml_uptodate) =
                        thy_unchanged t thy_file ml_file;
            in if thy_uptodate andalso ml_uptodate then ()
                                                   else use_thy t;
               reload_changed ts
            end
        | reload_changed [] = ();

     (*Remove all theories that are no descendants of Pure.
       If there are still children in the deleted theory's list
       schedule them for reloading *)
     fun collect_garbage not_garbage =
       let fun collect ((tname, ThyInfo {children, ...}) :: ts) =
                 if tname mem not_garbage then collect ts
                 else (writeln ("Theory \"" ^ tname
                         ^ "\" is no longer linked with Pure - removing it.");
                       remove_thy tname;
                       seq mark_outdated children)
             | collect [] = ()

       in collect (Symtab.dest (!loaded_thys)) end;
  in collect_garbage ("Pure" :: (load_order ["Pure"] []));
     reload_changed (load_order ["Pure"] [])
  end;

(*Merge theories to build a base for a new theory.
  Base members are only loaded if they are missing. *)
fun mk_base bases child mk_draft =
      let (*List all descendants of a theory list *)
          fun list_descendants (t :: ts) =
                let val tinfo = get_thyinfo t
                in if is_some tinfo then
                     let val ThyInfo {children, ...} = the tinfo
                     in children union (list_descendants (ts union children))
                     end
                   else []
                end
            | list_descendants [] = [];

          (*Show the cycle that would be created by add_child *)
          fun show_cycle base =
            let fun find_it result curr =
                  let val tinfo = get_thyinfo curr
                  in if base = curr then
                       error ("Cyclic dependency of theories: "
                              ^ child ^ "->" ^ base ^ result)
                     else if is_some tinfo then
                       let val ThyInfo {children, ...} = the tinfo
                       in seq (find_it ("->" ^ curr ^ result)) children
                       end
                     else ()
                  end
            in find_it "" child end;

          (*Check if a cycle would be created by add_child *)
          fun find_cycle base =
            if base mem (list_descendants [child]) then show_cycle base
            else ();

          (*Add child to child list of base *)
          fun add_child base =
            let val tinfo =
                  case Symtab.lookup (!loaded_thys, base) of
                      Some (ThyInfo {path, children, thy_time, ml_time,
                                     theory, thms}) =>
                        ThyInfo {path = path, children = child ins children,
                                 thy_time = thy_time, ml_time = ml_time,
                                 theory = theory, thms = thms}
                    | None => ThyInfo {path = "", children = [child],
                                       thy_time = None, ml_time = None,
                                       theory = None, thms = Symtab.null};
            in loaded_thys := Symtab.update ((base, tinfo), !loaded_thys) end;

          (*Load a base theory if not already done
            and no cycle would be created *)
          fun load base =
              let val thy_present = already_loaded base
                                           (*test this before child is added *)
              in
                if child = base then
                    error ("Cyclic dependency of theories: " ^ child
                           ^ "->" ^ child)
                else
                  (find_cycle base;
                   add_child base;
                   if thy_present then ()
                   else (writeln ("Autoloading theory " ^ (quote base)
                                  ^ " (used by " ^ (quote child) ^ ")");
                         use_thy base)
                  )
              end;

          (*Load all needed files and make a list of all real theories *)
          fun load_base (Thy b :: bs) =
               (load b;
                b :: (load_base bs))
            | load_base (File b :: bs) =
               (load b;
                load_base bs)    (*don't add it to merge_theories' parameter *)
            | load_base [] = [];

          (*Get theory object for a loaded theory *)
          fun get_theory name =
            let val ThyInfo {theory, ...} = the (get_thyinfo name)
            in the theory end;

          val mergelist = (unlink_thy child;
                           load_base bases);
     in writeln ("Loading theory " ^ (quote child));
        merge_thy_list mk_draft (map get_theory mergelist) end;

(*Change theory object for an existent item of loaded_thys
  or create a new item *)
fun store_theory (thy, tname) =
  let val tinfo = case Symtab.lookup (!loaded_thys, tname) of
               Some (ThyInfo {path, children, thy_time, ml_time, thms, ...}) =>
                 ThyInfo {path = path, children = children,
                          thy_time = thy_time, ml_time = ml_time,
                          theory = Some thy, thms = thms}
             | None => ThyInfo {path = "", children = [],
                                thy_time = Some "", ml_time = Some "",
                                theory = Some thy, thms = Symtab.null};
  in loaded_thys := Symtab.update ((tname, tinfo), !loaded_thys) end;



(** store and retrieve theorems **)

(* thyinfo_of_sign *)

fun thyinfo_of_sign sg =
  let
    val ref xname = hd (#stamps (Sign.rep_sg sg));
    val opt_info = get_thyinfo xname;

    fun eq_sg (ThyInfo {theory = None, ...}) = false
      | eq_sg (ThyInfo {theory = Some thy, ...}) = Sign.eq_sg (sg, sign_of thy);

    val show_sg = Pretty.str_of o Sign.pretty_sg;
  in
    if is_some opt_info andalso eq_sg (the opt_info) then
      (xname, the opt_info)
    else
      (case Symtab.find_first (eq_sg o snd) (! loaded_thys) of
        Some name_info => name_info
      | None => error ("Theory " ^ show_sg sg ^ " not stored by loader"))
  end;


(* theory_of_sign, theory_of_thm *)

fun theory_of_sign sg =
  (case thyinfo_of_sign sg of
    (_, ThyInfo {theory = Some thy, ...}) => thy
  | _ => sys_error "theory_of_sign");

val theory_of_thm = theory_of_sign o #sign o rep_thm;


(* store theorems *)

(*store a theorem in the thy_info of its theory*)
fun store_thm (name, thm) =
  let
    val (thy_name, ThyInfo {path, children, thy_time, ml_time, theory, thms}) =
      thyinfo_of_sign (#sign (rep_thm thm));
    val thms' = Symtab.update_new ((name, thm), thms)
      handle Symtab.DUPLICATE s => error ("Duplicate theorem name " ^ quote s);
  in
    loaded_thys := Symtab.update
      ((thy_name, ThyInfo {path = path, children = children,
        thy_time = thy_time, ml_time = ml_time, theory = theory, thms = thms'}),
        ! loaded_thys);
    thm
  end;

(*store result of proof in loaded_thys and as ML value*)
fun qed name =
  use_string ["val " ^ name ^ " = store_thm (" ^ quote name ^ ", result ());"];


(* retrieve theorems *)

fun thmtab thy =
  let val (_, ThyInfo {thms, ...}) = thyinfo_of_sign (sign_of thy)
  in thms end;

(*get a stored theorem specified by theory and name*)
fun get_thm thy name =
  (case Symtab.lookup (thmtab thy, name) of
    Some thm => thm
  | None => raise THEORY ("get_thm: no theorem " ^ quote name, [thy]));

(*get stored theorems of a theory*)
val thms_of = Symtab.dest o thmtab;


end;

