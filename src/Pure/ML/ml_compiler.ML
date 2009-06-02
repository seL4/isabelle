(*  Title:      Pure/ML/ml_compiler.ML
    Author:     Makarius

Runtime compilation -- generic version.
*)

signature ML_COMPILER =
sig
  val eval: bool -> Position.T -> ML_Lex.token list -> unit
end

structure ML_Compiler: ML_COMPILER =
struct

fun eval verbose pos toks =
  let
    val line = the_default 1 (Position.line_of pos);
    val file = the_default "ML" (Position.file_of pos);
    val text = ML_Lex.flatten toks;
  in Secure.use_text ML_Env.local_context (line, file) verbose text end;

end;

