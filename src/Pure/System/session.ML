(*  Title:      Pure/System/session.ML
    Author:     Markus Wenzel, TU Muenchen

Session management -- maintain state of logic images.
*)

signature SESSION =
sig
  val id: unit -> string list
  val name: unit -> string
  val welcome: unit -> string
  val finish: unit -> unit
  val init: bool -> bool -> bool -> string -> string -> bool -> string -> (string * string) list ->
    string -> string -> string * Present.dump_mode -> string -> bool -> unit
  val with_timing: string -> bool -> ('a -> 'b) -> 'a -> 'b
  val use_dir: string -> string -> bool -> string list -> bool -> bool -> string ->
    string -> bool -> string list -> string -> string -> bool * string ->
    string -> int -> bool -> bool -> int -> int -> int -> int -> unit
end;

structure Session: SESSION =
struct

(* session state *)

val session = Unsynchronized.ref ([Context.PureN]: string list);
val session_finished = Unsynchronized.ref false;

fun id () = ! session;
fun name () = "Isabelle/" ^ List.last (! session);


(* access path *)

val session_path = Unsynchronized.ref ([]: string list);
val remote_path = Unsynchronized.ref (NONE: Url.T option);

fun path () = ! session_path;


(* welcome *)

fun welcome () =
  if Distribution.is_official then
    "Welcome to " ^ name () ^ " (" ^ Distribution.version ^ ")"
  else "Unofficial version of " ^ name () ^ " (" ^ Distribution.version ^ ")";


(* add_path *)

fun add_path reset s =
  let val sess = ! session @ [s] in
    (case duplicates (op =) sess of
      [] => (session := sess; session_path := ((if reset then [] else ! session_path) @ [s]))
    | dups => error ("Duplicate session identifiers " ^ commas_quote dups))
  end;


(* init_name *)

fun init_name reset parent name =
  if not (member (op =) (! session) parent) orelse not (! session_finished) then
    error ("Unfinished parent session " ^ quote parent ^ " for " ^ quote name)
  else (add_path reset name; session_finished := false);


(* finish *)

fun finish_futures () =
  (case map_filter Task_Queue.group_status (Goal.reset_futures ()) of
    [] => ()
  | exns => raise Par_Exn.make exns);

fun finish () =
 (Future.shutdown ();
  finish_futures ();
  Thy_Info.finish ();
  Present.finish ();
  Keyword.status ();
  Outer_Syntax.check_syntax ();
  Options.reset_default ();
  session_finished := true);


(* use_dir *)

fun with_timing _ false f x = f x
  | with_timing item true f x =
      let
        val start = Timing.start ();
        val y = f x;
        val timing = Timing.result start;
        val factor = Time.toReal (#cpu timing) / Time.toReal (#elapsed timing)
          |> Real.fmt (StringCvt.FIX (SOME 2));
        val _ =
          Output.physical_stderr ("Timing " ^ item ^ " (" ^
            string_of_int (Multithreading.max_threads_value ()) ^ " threads, " ^
            Timing.message timing ^ ", factor " ^ factor ^ ")\n");
      in y end;

fun get_rpath rpath =
  (if rpath = "" then () else
     if is_some (! remote_path) then
       error "Path for remote theory browsing information may only be set once"
     else
       remote_path := SOME (Url.explode rpath);
   (! remote_path, rpath <> ""));

fun init build reset info info_path doc doc_graph doc_output doc_variants
    parent name doc_dump rpath verbose =
 (init_name reset parent name;
  Present.init build info info_path (if doc = "false" then "" else doc) doc_graph doc_output
    doc_variants (path ()) name doc_dump (get_rpath rpath) verbose
    (map Thy_Info.get_theory (Thy_Info.get_names ())));

local

fun doc_dump (cp, dump) = (dump, if cp then Present.Dump_all else Present.Dump_tex_sty);

fun read_variants strs =
  rev (distinct (eq_fst (op =)) (rev (("document", "") :: map Present.read_variant strs)))
  |> filter_out (fn (_, s) => s = "-");

in

fun use_dir item root build modes reset info info_path doc doc_graph doc_variants parent
    name dump rpath level timing verbose max_threads trace_threads
    parallel_proofs parallel_proofs_threshold =
  ((fn () =>
    let
      val _ =
        Output.physical_stderr
          "### Legacy feature: old \"isabelle usedir\" -- use \"isabelle build\" instead!\n";
      val _ =
        init build reset info info_path doc doc_graph "" (read_variants doc_variants) parent name
          (doc_dump dump) rpath verbose;
      val res1 = (use |> with_timing item timing |> Exn.capture) root;
      val res2 = Exn.capture finish ();
    in ignore (Par_Exn.release_all [res1, res2]) end)
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

end;
