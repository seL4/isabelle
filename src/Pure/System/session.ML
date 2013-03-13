(*  Title:      Pure/System/session.ML
    Author:     Markus Wenzel, TU Muenchen

Session management -- internal state of logic images.
*)

signature SESSION =
sig
  val name: unit -> string
  val welcome: unit -> string
  val init: bool -> bool -> Path.T -> string -> bool -> string -> (string * string) list ->
    string -> string * string -> bool * string -> bool -> unit
  val finish: unit -> unit
  val with_timing: string -> bool -> ('a -> 'b) -> 'a -> 'b
  val use_dir: string -> string -> bool -> string list -> bool -> bool -> string ->
    string -> bool -> string list -> string -> string -> bool * string ->
    string -> int -> bool -> bool -> int -> int -> int -> int -> unit
end;

structure Session: SESSION =
struct

(* session state *)

val session = Unsynchronized.ref {chapter = "Pure", name = "Pure"};
val session_finished = Unsynchronized.ref false;

fun name () = "Isabelle/" ^ #name (! session);

fun welcome () =
  if Distribution.is_official then
    "Welcome to " ^ name () ^ " (" ^ Distribution.version ^ ")"
  else "Unofficial version of " ^ name () ^ " (" ^ Distribution.version ^ ")";


(* init *)

fun init build info info_path doc doc_graph doc_output doc_variants
    parent (chapter, name) doc_dump verbose =
  if #name (! session) <> parent orelse not (! session_finished) then
    error ("Unfinished parent session " ^ quote parent ^ " for " ^ quote name)
  else
    let
      val _ = session := {chapter = chapter, name = name};
      val _ = session_finished := false;
    in
      Present.init build info info_path (if doc = "false" then "" else doc)
        doc_graph doc_output doc_variants (chapter, name)
        doc_dump verbose (map Thy_Info.get_theory (Thy_Info.get_names ()))
    end;


(* finish *)

fun finish () =
 (Goal.shutdown_futures ();
  Thy_Info.finish ();
  Present.finish ();
  Keyword.status ();
  Outer_Syntax.check_syntax ();
  Options.reset_default ();
  Future.shutdown ();
  session_finished := true);


(* timing within ML *)

fun with_timing name verbose f x =
  let
    val start = Timing.start ();
    val y = f x;
    val timing = Timing.result start;

    val threads = string_of_int (Multithreading.max_threads_value ());
    val factor = Time.toReal (#cpu timing) / Time.toReal (#elapsed timing)
      |> Real.fmt (StringCvt.FIX (SOME 2));

    val timing_props =
      [("threads", threads)] @ Markup.timing_properties timing @ [("factor", factor)];
    val _ = writeln ("\fTiming = " ^ YXML.string_of_body (XML.Encode.properties timing_props));
    val _ =
      if verbose then
        Output.physical_stderr ("Timing " ^ name ^ " (" ^
          threads ^ " threads, " ^ Timing.message timing ^ ", factor " ^ factor ^ ")\n")
      else ();
  in y end;


(* use_dir *)

fun read_variants strs =
  rev (distinct (eq_fst (op =)) (rev (("document", "") :: map Present.read_variant strs)))
  |> filter_out (fn (_, s) => s = "-");

fun use_dir item root build modes reset info info_path doc doc_graph doc_variants parent
    name doc_dump rpath level timing verbose max_threads trace_threads
    parallel_proofs parallel_subproofs_saturation =
  ((fn () =>
    let
      val _ =
        Output.physical_stderr
          "### Legacy feature: old \"isabelle usedir\" -- use \"isabelle build\" instead!\n";
      val _ =
        if not reset then ()
        else Output.physical_stderr "### Ignoring reset (historic usedir option -r)\n";
      val _ =
        if rpath = "" then ()
        else Output.physical_stderr "### Ignoring remote path (historic usedir option -P)\n";

      val _ =
        init build info (Path.explode info_path) doc doc_graph "" (read_variants doc_variants)
          parent ("Unsorted", name) doc_dump verbose;
      val res1 = (use |> with_timing item timing |> Exn.capture) root;
      val res2 = Exn.capture finish ();
    in ignore (Par_Exn.release_all [res1, res2]) end)
    |> Unsynchronized.setmp Proofterm.proofs level
    |> Unsynchronized.setmp print_mode (modes @ print_mode_value ())
    |> Unsynchronized.setmp Goal.parallel_proofs parallel_proofs
    |> Unsynchronized.setmp Goal.parallel_subproofs_saturation parallel_subproofs_saturation
    |> Unsynchronized.setmp Multithreading.trace trace_threads
    |> Unsynchronized.setmp Multithreading.max_threads
      (if Multithreading.available then max_threads
       else (if max_threads = 1 then () else warning "Multithreading support unavailable"; 1))) ()
  handle exn => (Output.error_msg (ML_Compiler.exn_message exn); exit 1);

end;
