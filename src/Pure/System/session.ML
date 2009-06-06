(*  Title:      Pure/System/session.ML
    Author:     Markus Wenzel, TU Muenchen

Session management -- maintain state of logic images.
*)

signature SESSION =
sig
  val id: unit -> string list
  val name: unit -> string
  val welcome: unit -> string
  val use_dir: string -> bool -> string list -> bool -> bool -> string -> bool -> string list ->
    string -> string -> bool * string -> string -> int -> bool -> int -> int -> bool -> unit
  val finish: unit -> unit
end;

structure Session: SESSION =
struct


(* session state *)

val session = ref ([Context.PureN]: string list);
val session_path = ref ([]: string list);
val session_finished = ref false;
val remote_path = ref (NONE: Url.T option);


(* access path *)

fun id () = ! session;
fun path () = ! session_path;

fun str_of [] = Context.PureN
  | str_of elems = space_implode "/" elems;

fun name () = "Isabelle/" ^ str_of (path ());


(* welcome *)

fun welcome () =
  if Distribution.is_official then
    "Welcome to " ^ name () ^ " (" ^ Distribution.version ^ ")"
  else
    "Unofficial version of " ^ name () ^ " (" ^ Distribution.version ^ ")" ^
    (if Distribution.changelog <> "" then "\nSee also " ^ Distribution.changelog else "");

val _ =
  OuterSyntax.improper_command "welcome" "print welcome message" OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative (writeln o welcome)));


(* add_path *)

fun add_path reset s =
  let val sess = ! session @ [s] in
    (case duplicates (op =) sess of
      [] => (session := sess; session_path := ((if reset then [] else ! session_path) @ [s]))
    | dups => error ("Duplicate session identifiers " ^ commas_quote dups ^ " in " ^ str_of sess))
  end;


(* init *)

fun init reset parent name =
  if not (member (op =) (! session) parent) orelse not (! session_finished) then
    error ("Unfinished parent session " ^ quote parent ^ " for " ^ quote name)
  else (add_path reset name; session_finished := false);


(* finish *)

fun finish () =
  (Output.accumulated_time ();
    ThyInfo.finish ();
    Present.finish ();
    Future.shutdown ();
    session_finished := true);


(* use_dir *)

fun get_rpath rpath =
  (if rpath = "" then () else
     if is_some (! remote_path) then
       error "Path for remote theory browsing information may only be set once"
     else
       remote_path := SOME (Url.explode rpath);
   (! remote_path, rpath <> ""));

fun dumping (_, "") = NONE
  | dumping (cp, path) = SOME (cp, Path.explode path);

fun use_dir root build modes reset info doc doc_graph doc_versions
    parent name dump rpath level verbose max_threads trace_threads parallel_proofs =
  ((fn () =>
     (init reset parent name;
      Present.init build info doc doc_graph doc_versions (path ()) name
        (dumping dump) (get_rpath rpath) verbose (map ThyInfo.get_theory (ThyInfo.get_names ()));
      use root;
      finish ()))
    |> setmp_noncritical Proofterm.proofs level
    |> setmp_noncritical print_mode (modes @ print_mode_value ())
    |> setmp_noncritical Goal.parallel_proofs parallel_proofs
    |> setmp_noncritical Multithreading.trace trace_threads
    |> setmp_noncritical Multithreading.max_threads
      (if Multithreading.available then max_threads
       else (if max_threads = 1 then () else warning "Multithreading support unavailable"; 1))) ()
  handle exn => (Output.error_msg (ML_Compiler.exn_message exn); exit 1);

end;
