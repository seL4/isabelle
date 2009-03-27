(*  Title:      Pure/ML-Systems/ml_pretty.ML
    Author:     Makarius

Raw datatype for ML pretty printing.
*)

structure ML_Pretty =
struct

datatype pretty =
  Block of (string * string) * pretty list * int |
  String of string * int |
  Break of bool * int;

end;

