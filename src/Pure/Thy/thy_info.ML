(*  Title:      Pure/Thy/thy_info.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Theory loader database: theory and file dependencies, theory values
and user data.

TODO:
  - check all these versions of 'use' (!!);
  - data: ThyInfoFun;
  - remove operation (GC!?);
  - update_all operation (!?);
  - put_theory:
      . include data;
      . allow for undef entry only;
      . elim (via theory_ref);
  - stronger handling of missing files (!?!?);
  - register_theory: do not require finished parents (!?) (no?);
  - observe verbose flag;
*)

signature BASIC_THY_INFO =
sig
  val theory: string -> theory
  val theory_of_sign: Sign.sg -> theory
  val theory_of_thm: thm -> theory
  val touch_thy: string -> unit
  val use_thy: string -> unit
  val update_thy: string -> unit
  val time_use_thy: string -> unit
end;

signature THY_INFO =
sig
  include BASIC_THY_INFO
  val verbose: bool ref
  val names: unit -> string list
  val get_theory: string -> theory
  val put_theory: theory -> unit
  val load_file: Path.T -> unit
  val use_thy_only: string -> unit
  val begin_theory: string -> string list -> theory
  val end_theory: theory -> theory
  val finish_all: unit -> unit
  val register_theory: theory -> unit
end;

signature PRIVATE_THY_INFO =
sig
  include THY_INFO
(* FIXME
  val init_data: Object.kind -> (Object.T * (Object.T -> Object.T) *
    (Object.T * Object.T -> Object.T) * (Sign.sg -> Object.T -> unit)) -> unit
  val print_data: Object.kind -> string -> unit
  val get_data: Object.kind -> (Object.T -> 'a) -> string -> 'a
  val put_data: Object.kind -> ('a -> Object.T) -> 'a -> unit
*)
end;

structure ThyInfo: PRIVATE_THY_INFO =
struct


(** thy database **)

(* messages *)

val verbose = ref false;

fun gen_msg txt [] = txt
  | gen_msg txt names = txt ^ " " ^ commas_quote names;

fun loader_msg txt names = gen_msg ("Theory loader: " ^ txt) names;

val show_path = space_implode " via " o map quote;
fun cycle_msg name names = loader_msg ("cyclic dependency of " ^ show_path (name :: names)) [];


(* derived graph operations *)		(* FIXME more abstract (!?) *)

fun add_deps name parents G =
  foldl (fn (H, parent) => Graph.add_edge_acyclic (parent, name) H) (G, parents)
    handle Graph.CYCLES namess => error (cat_lines (map (cycle_msg name) namess));

fun del_deps name G =           (* FIXME GC (!?!?) *)
  foldl (fn (H, parent) => Graph.del_edge (parent, name) H) (G, Graph.imm_preds G name);

fun update_node name parents entry G =
  add_deps name parents
    (if can (Graph.get_node G) name then del_deps name G else Graph.new_node (name, entry) G);


(* thy database *)

type deps =
  {present: bool, outdated: bool,
    master: File.info option, files: (Path.T * File.info option) list} option;

fun make_depends present outdated master files =
  Some {present = present, outdated = outdated, master = master, files = files}: deps;

type thy = deps * (theory * Object.T Symtab.table) option;
type kind = Object.kind * (Object.T * (Object.T -> unit));


local
  val database = ref (Graph.empty: thy Graph.T, Symtab.empty: kind Symtab.table);
in

fun get_thys () = #1 (! database);
fun get_kinds () = #2 (! database);
fun change_thys f = database := (f (get_thys ()), get_kinds ());
fun change_kinds f = database := (get_thys (), f (get_kinds ()));

end;


(* access thy graph *)

fun thy_graph f x = f (get_thys ()) x;
fun get_names () = map #1 (Graph.get_nodes (get_thys ()));


(* access thy *)

fun lookup_thy name = Some (thy_graph Graph.get_node name) handle Graph.UNDEFINED _ => None;

fun get_thy name =
  (case lookup_thy name of
    Some thy => thy
  | None => error (loader_msg "nothing known about theory" [name]));

fun change_thy name f = (get_thy name; change_thys (Graph.map_node name f));


(* access deps *)

val lookup_deps = apsome #1 o lookup_thy;
val get_deps = #1 o get_thy;
fun change_deps name f = change_thy name (fn (deps, x) => (f deps, x));

fun get_files name = (case get_deps name of Some {files, ...} => files | _ => []);
fun is_finished name = is_none (get_deps name);


(* access theory *)

fun get_theory name =
  (case get_thy name of
    (_, Some (theory, _)) => theory
  | _ => error (loader_msg "undefined theory entry for" [name]));

val theory_of_sign = get_theory o Sign.name_of;
val theory_of_thm = theory_of_sign o Thm.sign_of_thm;

fun put_theory theory =
  change_thy (PureThy.get_name theory) (fn (deps, _) => (deps, (Some (theory, Symtab.empty))));



(** thy data **)  (* FIXME *)



(** thy operations **)

fun FIXME msg = writeln ("DEBUG:\n" ^ msg);


(* touch_thy -- mark as outdated *)

fun touch_thy name = change_deps name
  (fn None => (warning (loader_msg "tried to touch finished theory" [name]); None)
    | Some {present, outdated = _, master, files} =>
        make_depends present true master files);


(* load_thy *)

fun required_by [] = ""
  | required_by initiators = " (required by " ^ show_path (rev initiators) ^ ")";

fun load_thy ml time initiators name parents =
  let
    val _ = if name mem_string initiators then error (cycle_msg name (rev initiators)) else ();
    val _ = writeln ("Loading theory " ^ quote name ^ required_by initiators);

    val _ = seq touch_thy (thy_graph Graph.all_succs [name]);
    val master = ThyLoad.load_thy name ml time;

    val files = get_files name;
    val missing_files = mapfilter (fn (path, None) => Some (Path.pack path) | _ => None) files;
  in
    if null missing_files then ()
    else warning (loader_msg ("unresolved dependencies on file(s) " ^ commas_quote missing_files ^
      "\nfor theory") [name]);
    change_deps name (fn _ => make_depends true false (Some master) files)
  end;


(* load_file *)

fun load_file path =
  let
    fun provide name info (deps as Some {present, outdated, master, files}) =
          if exists (equal path o #1) files then
            make_depends present outdated master (overwrite (files, (path, Some info)))
          else (warning (loader_msg ("undeclared dependency on file " ^ quote (Path.pack path) ^
            "\nfor theory") [name]); deps)
      | provide _ _ None = None;
  in
    (case apsome PureThy.get_name (Context.get_context ()) of
      None => (ThyLoad.load_file path; ())
    | Some name =>
        if is_some (lookup_thy name) then change_deps name (provide name (ThyLoad.load_file path))
        else (ThyLoad.load_file path; ()))
  end;


(* require_thy *)

fun init_deps master files = make_depends false false master (map (rpair None) files);

fun load_deps name ml =
  let val (master, (parents, files)) = ThyLoad.deps_thy name ml
  in (Some (init_deps (Some master) files), parents) end;

fun file_current (_, None) = false
  | file_current (path, info) = info = ThyLoad.check_file path;

fun current_deps ml strict name =
  (case lookup_deps name of
    None => (false, load_deps name ml)
  | Some deps =>
      let val same_deps = (None, thy_graph Graph.imm_preds name) in
        (case deps of
          None => (true, same_deps)
        | Some {present, outdated, master, files} =>
            if present andalso not strict then (true, same_deps)
            else
              let val master' = Some (ThyLoad.check_thy name ml) in
                if master <> master' then (false, load_deps name ml)
                else (not outdated andalso forall file_current files, same_deps)
              end)
      end);

fun outdated name =
  (case lookup_deps name of Some (Some {outdated, ...}) => outdated | _ => false);

fun untouch None = None
  | untouch (Some {present, outdated = _, master, files}) =
      make_depends present false master files;

fun require_thy ml time strict keep_strict initiators name =
  let
    val require_parent =
      require_thy ml time (strict andalso keep_strict) keep_strict (name :: initiators);
    val (current, (new_deps, parents)) = current_deps ml strict name handle ERROR =>
      error (loader_msg "The error(s) above occurred while examining theory" [name] ^ "\n" ^
        required_by initiators);
    val pre_outdated = outdated name;
  in
    seq require_parent parents;
    if current andalso pre_outdated = outdated name then ()	(* FIXME ?? *)
    else
      ((case new_deps of
        Some deps => change_thys (update_node name parents (untouch deps, None))
      | None => ()); load_thy ml time initiators name parents)
  end;

val weak_use_thy = require_thy true false false false [];
val use_thy      = require_thy true false true false [];
val update_thy   = require_thy true false true true [];
val time_use_thy = require_thy true true true false [];
val use_thy_only = require_thy false false true false [];


(* begin / end theory *)		(* FIXME tune *)

fun begin_theory name parents =
  let
    val _ = seq weak_use_thy parents;
    val theory = PureThy.begin_theory name (map get_theory parents);
    val _ = change_thys (update_node name parents (init_deps None [], Some (theory, Symtab.empty)));
  in theory end;

fun end_theory theory =
  let val theory' = PureThy.end_theory theory
  in put_theory theory'; theory' end;


(* finish entries *)

(* FIXME
fun finishs names =
  let
    fun err txt bads =
      error (loader_msg txt bads ^ "\n" ^ gen_msg "cannot mark" names ^ " as finished");

    val all_preds = thy_graph Graph.all_preds names;
    val noncurrent = filter_out is_current all_preds;
    val unfinished = filter_out is_finished (all_preds \\ names);
  in
    if not (null noncurrent) then err "non-current theories" noncurrent
    else if not (null unfinished) then err "unfinished ancestor theories" unfinished
    else seq (fn name => change_thy name (apfst (K Finished)))
  end;

fun finish name = finishs [name];
*)

fun update_all () = ();         (* FIXME fake *)

fun finish_all () = (update_all (); change_thys (Graph.map_nodes (fn (_, entry) => (None, entry))));


(* register existing theories *)

fun register_theory theory =
  let
    val name = PureThy.get_name theory;
    val parents = Theory.parents_of theory;
    val parent_names = map PureThy.get_name parents;

    fun err txt bads =
      error (loader_msg txt bads ^ "\n" ^ gen_msg "cannot register theory" [name]);

    val unfinished = filter_out is_finished parent_names;
    fun get_variant (x, y_name) =
      if Theory.eq_thy (x, get_theory y_name) then None
      else Some y_name;
    val variants = mapfilter get_variant (parents ~~ parent_names);

    fun register G =
      (Graph.new_node (name, (None, Some (theory, Symtab.empty))) G
        handle Graph.DUPLICATE _ => err "duplicate theory entry" [])
      |> add_deps name parent_names;
  in
    if not (null unfinished) then err "unfinished parent theories" unfinished
    else if not (null variants) then err "different versions of parent theories" variants
    else change_thys register
  end;


(*final declarations of this structure*)
val theory = get_theory;
val names = get_names;

end;

structure BasicThyInfo: BASIC_THY_INFO = ThyInfo;
open BasicThyInfo;
