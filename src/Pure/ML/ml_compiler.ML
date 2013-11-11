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
  val eval: bool -> Position.T -> ML_Lex.token list -> unit
end

structure ML_Compiler: ML_COMPILER =
struct

val exn_info =
 {exn_position = fn _: exn => Position.none,
  pretty_exn = Pretty.str o General.exnMessage};

val exn_messages_ids = Runtime.exn_messages_ids exn_info;
val exn_messages = Runtime.exn_messages exn_info;
val exn_message = Runtime.exn_message exn_info;

val exn_error_message = Output.error_message o exn_message;
fun exn_trace e = print_exception_trace exn_message e;

fun eval verbose pos toks =
  let
    val line = the_default 1 (Position.line_of pos);
    val file = the_default "ML" (Position.file_of pos);
    val text = ML_Lex.flatten toks;
  in Secure.use_text ML_Env.local_context (line, file) verbose text end;

end;

