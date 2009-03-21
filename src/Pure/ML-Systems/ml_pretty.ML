(*  Title:      Pure/ML-Systems/ml_pretty.ML
    Author:     Makarius

Datatype for ML pretty printing (cf. mlsource/MLCompiler/Pretty.sml in
Poly/ML 5.3).
*)

structure ML_Pretty =
struct

datatype context =
  ContextLocation of
    {file: string, startLine: int, startPosition: int, endLine: int, endPosition: int} |
  ContextParentStructure of string * context list;

datatype pretty =
  PrettyBlock of int * bool * context list * pretty list |
  PrettyBreak of int * int |
  PrettyString of string;

end;

