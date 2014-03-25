(*  Title:      Pure/ML/ml_compiler.ML
    Author:     Makarius

Runtime compilation -- generic version.
*)

signature ML_COMPILER =
sig
  val exn_messages_ids: exn -> Runtime.error list
  val exn_messages: exn -> (serial * string) list
  val exn_message: exn -> string
  val exn_error_message: exn -> unit
  val exn_trace: (unit -> 'a) -> 'a
  val print_depth_raw: Config.raw
  val print_depth: int Config.T
  val get_print_depth: unit -> int
  type flags = {SML: bool, verbose: bool}
  val eval: flags -> Position.T -> ML_Lex.token list -> unit
end

structure ML_Compiler: ML_COMPILER =
struct

(* exceptions *)

val exn_info =
 {exn_position = fn _: exn => Position.none,
  pretty_exn = Pretty.str o General.exnMessage};

val exn_messages_ids = Runtime.exn_messages_ids exn_info;
val exn_messages = Runtime.exn_messages exn_info;
val exn_message = Runtime.exn_message exn_info;

val exn_error_message = Output.error_message o exn_message;
fun exn_trace e = print_exception_trace exn_message e;


(* print depth *)

val print_depth_raw =
  Config.declare "ML_print_depth" (fn _ => Config.Int (get_default_print_depth ()));
val print_depth = Config.int print_depth_raw;

fun get_print_depth () =
  (case Context.thread_data () of
    NONE => get_default_print_depth ()
  | SOME context => Config.get_generic context print_depth);


(* eval *)

type flags = {SML: bool, verbose: bool};

fun eval {SML, verbose} pos toks =
  let
    val _ = if SML then error ("Standard ML is unsupported on " ^ ML_System.name) else ();
    val line = the_default 1 (Position.line_of pos);
    val file = the_default "ML" (Position.file_of pos);
    val text = ML_Lex.flatten toks;
  in Secure.use_text ML_Env.local_context (line, file) verbose text end;

end;

