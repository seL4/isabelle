(*  Title:      Pure/ML-Systems/polyml.ML

Compatibility wrapper for experimental versions of Poly/ML after 5.2.1.
*)

open Thread;
use "ML-Systems/polyml_common.ML";
use "ML-Systems/multithreading_polyml.ML";

val pointer_eq = PolyML.pointerEq;

fun share_common_data () = PolyML.shareCommonData PolyML.rootFunction;


(* runtime compilation *)

structure ML_NameSpace =
struct
  open PolyML.NameSpace;
  val global = PolyML.globalNameSpace;
end;

local

fun drop_newline s =
  if String.isSuffix "\n" s then String.substring (s, 0, size s - 1)
  else s;

in

fun use_text (tune: string -> string) str_of_pos
    name_space (start_line, name) (print, err) verbose txt =
  let
    val current_line = ref start_line;
    val in_buffer = ref (String.explode (tune txt));
    val out_buffer = ref ([]: string list);
    fun output () = drop_newline (implode (rev (! out_buffer)));

    fun get () =
      (case ! in_buffer of
        [] => NONE
      | c :: cs =>
          (in_buffer := cs; if c = #"\n" then current_line := ! current_line + 1 else (); SOME c));
    fun put s = out_buffer := s :: ! out_buffer;
    fun put_message {message, hard, location = {startLine = line, ...}, context} =
     (put (if hard then "Error: " else "Warning: ");
      PolyML.prettyPrint (put, 76) message;
      put (str_of_pos line name ^ "\n"));

    val parameters =
     [PolyML.Compiler.CPOutStream put,
      PolyML.Compiler.CPLineNo (fn () => ! current_line),
      PolyML.Compiler.CPErrorMessageProc put_message,
      PolyML.Compiler.CPNameSpace name_space,
      PolyML.Compiler.CPPrintInAlphabeticalOrder false];
    val _ =
      (while not (List.null (! in_buffer)) do
        PolyML.compiler (get, parameters) ())
      handle exn =>
       (put ("Exception- " ^ General.exnMessage exn ^ " raised");
        err (output ()); raise exn);
  in if verbose then print (output ()) else () end;

fun use_file tune str_of_pos name_space output verbose name =
  let
    val instream = TextIO.openIn name;
    val txt = Exn.release (Exn.capture TextIO.inputAll instream before TextIO.closeIn instream);
  in use_text tune str_of_pos name_space (1, name) output verbose txt end;

end;


(* toplevel pretty printing *)

fun ml_pretty (ML_Pretty.Block (_, prts, ind)) = PrettyBlock (ind, false, [], map ml_pretty prts)
  | ml_pretty (ML_Pretty.String (s, _)) = PrettyString s
  | ml_pretty (ML_Pretty.Break (false, wd)) = PrettyBreak (wd, 0)
  | ml_pretty (ML_Pretty.Break (true, _)) = PrettyBreak (99999, 0);

fun toplevel_pp tune str_of_pos output (_: string list) pp =
  use_text tune str_of_pos ML_NameSpace.global (1, "pp") output false
    ("addPrettyPrinter (fn _ => fn _ => ml_pretty o Pretty.to_ML o (" ^ pp ^ "))");

