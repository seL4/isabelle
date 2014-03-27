(*  Title:      Pure/ML/ml_compiler.ML
    Author:     Makarius

Runtime compilation and evaluation -- generic version.
*)

signature ML_COMPILER =
sig
  type flags = {SML: bool, verbose: bool}
  val eval: flags -> Position.T -> ML_Lex.token list -> unit
end

structure ML_Compiler: ML_COMPILER =
struct

type flags = {SML: bool, verbose: bool};

fun eval {SML, verbose} pos toks =
  let
    val _ = if SML then error ("Standard ML is unsupported on " ^ ML_System.name) else ();
    val line = the_default 1 (Position.line_of pos);
    val file = the_default "ML" (Position.file_of pos);
    val text = ML_Lex.flatten toks;
  in Secure.use_text ML_Env.local_context (line, file) verbose text end;

end;

