(*  Title:      Pure/System/session.ML
    Author:     Markus Wenzel, TU Muenchen

Session management -- maintain state of logic images.
*)

signature SESSION =
sig
  val id: unit -> string list
  val name: unit -> string
  val welcome: unit -> string
  val init: bool -> string -> string -> unit
  val use_dir: string -> string -> bool -> string list -> bool -> bool -> string ->
    string -> bool -> string list -> string -> string -> bool * string ->
    string -> int -> bool -> bool -> int -> int -> int -> int -> unit
  val finish: unit -> unit
end;

structure Session: SESSION =
struct


(* session state *)

val session = Unsynchronized.ref ([Context.PureN]: string list);
val session_path = Unsynchronized.ref ([]: string list);
val session_finished = Unsynchronized.ref false;
val remote_path = Unsynchronized.ref (NONE: Url.T option);


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
  Outer_Syntax.improper_command ("welcome", Keyword.diag) "print welcome message"
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
  (Thy_Info.finish ();
    Present.finish ();
    Outer_Syntax.check_syntax ();
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

fun use_dir item root build modes reset info info_path doc doc_graph doc_variants parent
    name dump rpath level timing verbose max_threads trace_threads
    parallel_proofs parallel_proofs_threshold =
  ((fn () =>
     (init reset parent name;
      Present.init build info info_path doc doc_graph doc_variants (path ()) name
        (dumping dump) (get_rpath rpath) verbose (map Thy_Info.get_theory (Thy_Info.get_names ()));
      if timing then
        let
          val start = Timing.start ();
          val _ = use root;
          val timing = Timing.result start;
          val factor = Time.toReal (#cpu timing) / Time.toReal (#elapsed timing)
            |> Real.fmt (StringCvt.FIX (SOME 2));
          val _ =
            Output.physical_stderr ("Timing " ^ item ^ " (" ^
              string_of_int (Multithreading.max_threads_value ()) ^ " threads, " ^
              Timing.message timing ^ ", factor " ^ factor ^ ")\n");
        in () end
      else use root;
      finish ()))
    |> Unsynchronized.setmp Proofterm.proofs level
    |> Unsynchronized.setmp print_mode (modes @ print_mode_value ())
    |> Unsynchronized.setmp Goal.parallel_proofs parallel_proofs
    |> Unsynchronized.setmp Goal.parallel_proofs_threshold parallel_proofs_threshold
    |> Unsynchronized.setmp Multithreading.trace trace_threads
    |> Unsynchronized.setmp Multithreading.max_threads
      (if Multithreading.available then max_threads
       else (if max_threads = 1 then () else warning "Multithreading support unavailable"; 1))) ()
  handle exn => (Output.error_msg (ML_Compiler.exn_message exn); exit 1);

end;
