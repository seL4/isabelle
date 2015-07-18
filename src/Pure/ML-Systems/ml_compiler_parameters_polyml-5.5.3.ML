(*  Title:      Pure/ML/ml_compiler_parameters_polyml-5.5.3.ML
    Author:     Makarius

Additional ML compiler parameters for Poly/ML 5.5.3, or later.
*)

structure ML_Compiler_Parameters: ML_COMPILER_PARAMETERS =
struct

fun debug b = [PolyML.Compiler.CPDebug b];

end;