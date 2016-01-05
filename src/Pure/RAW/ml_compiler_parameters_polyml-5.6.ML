(*  Title:      Pure/RAW/ml_compiler_parameters_polyml-5.6.ML
    Author:     Makarius

Additional ML compiler parameters for Poly/ML 5.6, or later.
*)

structure ML_Compiler_Parameters: ML_COMPILER_PARAMETERS =
struct

fun debug b = [PolyML.Compiler.CPDebug b];

end;