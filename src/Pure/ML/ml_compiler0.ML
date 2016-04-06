(*  Title:      Pure/ML/ml_compiler0.ML
    Author:     Makarius

Runtime compilation and evaluation for bootstrap.
Initial ML use operations.
*)

signature ML_COMPILER0 =
sig
  type polyml_location = PolyML.location
  type context =
   {name_space: ML_Name_Space.T,
    print_depth: int option,
    here: int -> string -> string,
    print: string -> unit,
    error: string -> unit}
  val make_context: ML_Name_Space.T -> context
  val use_text: context -> {debug: bool, file: string, line: int, verbose: bool} -> string -> unit
  val use_file: context -> {debug: bool, verbose: bool} -> string -> unit
  val debug_option: bool option -> bool
  val use_operations: (bool option -> string -> unit) ->
    {use: string -> unit, use_debug: string -> unit, use_no_debug: string -> unit}
end;

structure ML_Compiler0: ML_COMPILER0 =
struct

type polyml_location = PolyML.location;


(* global options *)

val _ = PolyML.Compiler.reportUnreferencedIds := true;
val _ = PolyML.Compiler.reportExhaustiveHandlers := true;
val _ = PolyML.Compiler.printInAlphabeticalOrder := false;
val _ = PolyML.Compiler.maxInlineSize := 80;


(* context *)

type context =
 {name_space: ML_Name_Space.T,
  print_depth: int option,
  here: int -> string -> string,
  print: string -> unit,
  error: string -> unit};

fun make_context name_space : context =
 {name_space = name_space,
  print_depth = NONE,
  here = fn line => fn file => " (line " ^ Int.toString line ^ " of \"" ^ file ^ "\")",
  print = fn s => (TextIO.output (TextIO.stdOut, s ^ "\n"); TextIO.flushOut TextIO.stdOut),
  error = fn s => error s};


(* use operations *)

local

fun drop_newline s =
  if String.isSuffix "\n" s then String.substring (s, 0, size s - 1)
  else s;

fun ml_input start_line name txt =
  let
    fun input line (#"@" :: #"{" :: #"h" :: #"e" :: #"r" :: #"e" :: #"}" :: cs) res =
          let val s = "(Position.line_file_only " ^ Int.toString line ^ " \"" ^ name ^ "\")"
          in input line cs (s :: res) end
      | input line (#"@" :: #"{" :: #"m" :: #"a" :: #"k" :: #"e" :: #"_" ::
            #"s" :: #"t" :: #"r" :: #"i" :: #"n" :: #"g" :: #"}" :: cs) res =
          input line cs (ML_Pretty.make_string_fn "" :: res)
      | input line (#"\\" :: #"<" :: cs) res = input line cs ("\092\092<" :: res)
      | input line (#"\n" :: cs) res = input (line + 1) cs ("\n" :: res)
      | input line (c :: cs) res = input line cs (str c :: res)
      | input _ [] res = rev res;
  in String.concat (input start_line (String.explode txt) []) end;

in

fun use_text ({name_space, print_depth, here, print, error, ...}: context)
    {line, file, verbose, debug} text =
  let
    val current_line = Unsynchronized.ref line;
    val in_buffer = Unsynchronized.ref (String.explode (ml_input line file text));
    val out_buffer = Unsynchronized.ref ([]: string list);
    fun output () = drop_newline (implode (rev (! out_buffer)));

    fun get () =
      (case ! in_buffer of
        [] => NONE
      | c :: cs =>
          (in_buffer := cs; if c = #"\n" then current_line := ! current_line + 1 else (); SOME c));
    fun put s = out_buffer := s :: ! out_buffer;
    fun put_message {message = msg1, hard, location = {startLine = message_line, ...}, context} =
     (put (if hard then "Error: " else "Warning: ");
      PolyML.prettyPrint (put, 76) msg1;
      (case context of NONE => () | SOME msg2 => PolyML.prettyPrint (put, 76) msg2);
      put ("At" ^ here (FixedInt.toInt message_line) file ^ "\n"));

    val parameters =
     [PolyML.Compiler.CPOutStream put,
      PolyML.Compiler.CPNameSpace name_space,
      PolyML.Compiler.CPErrorMessageProc put_message,
      PolyML.Compiler.CPLineNo (fn () => ! current_line),
      PolyML.Compiler.CPFileName file,
      PolyML.Compiler.CPPrintInAlphabeticalOrder false,
      PolyML.Compiler.CPDebug debug] @
     (case print_depth of NONE => [] | SOME d => [PolyML.Compiler.CPPrintDepth (fn () => d)]);
    val _ =
      (while not (List.null (! in_buffer)) do
        PolyML.compiler (get, parameters) ())
      handle exn =>
        if Exn.is_interrupt exn then Exn.reraise exn
        else
         (put ("Exception- " ^ General.exnMessage exn ^ " raised");
          error (output ()); Exn.reraise exn);
  in if verbose then print (output ()) else () end;

end;

fun use_file context {verbose, debug} file =
  let
    val instream = TextIO.openIn file;
    val text = Exn.release (Exn.capture TextIO.inputAll instream before TextIO.closeIn instream);
  in use_text context {line = 1, file = file, verbose = verbose, debug = debug} text end;

fun use_operations (use_ : bool option -> string -> unit) =
  {use = use_ NONE, use_debug = use_ (SOME true), use_no_debug = use_ (SOME false)};


fun debug_option NONE = OS.Process.getEnv "ISABELLE_ML_DEBUGGER" = SOME "true"
  | debug_option (SOME debug) = debug;

end;


(* initial use operations *)

val {use, use_debug, use_no_debug} =
  let val context = ML_Compiler0.make_context ML_Name_Space.global in
    ML_Compiler0.use_operations (fn opt_debug => fn file =>
      ML_Compiler0.use_file context
        {verbose = true, debug = ML_Compiler0.debug_option opt_debug} file
      handle ERROR msg => (#print context msg; raise error "ML error"))
  end;


(* export type-dependent functions *)

ML_Compiler0.use_text
  (ML_Compiler0.make_context
    (ML_Name_Space.global_values
      [("prettyRepresentation", "ML_system_pretty"),
       ("addPrettyPrinter", "ML_system_pp"),
       ("addOverload", "ML_system_overload")]))
  {debug = false, file = "", line = 0, verbose = false}
  "open PolyML RunCall" handle ERROR _ => ();
