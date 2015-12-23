(*  Title:      Pure/ML/ml_compiler_parameters.ML
    Author:     Makarius

Additional ML compiler parameters for Poly/ML.
*)

signature ML_COMPILER_PARAMETERS =
sig
  val debug: bool -> PolyML.Compiler.compilerParameters list
end;

structure ML_Compiler_Parameters: ML_COMPILER_PARAMETERS =
struct

fun debug _ = [];

end;