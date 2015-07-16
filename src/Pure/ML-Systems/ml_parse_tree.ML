(*  Title:      Pure/ML/ml_parse_tree.ML
    Author:     Makarius

Additional ML parse tree components for Poly/ML.
*)

signature ML_PARSE_TREE =
sig
  val completions: PolyML.ptProperties -> string list option
  val break_point: PolyML.ptProperties -> bool Unsynchronized.ref option
end;

structure ML_Parse_Tree: ML_PARSE_TREE =
struct

fun completions _ = NONE;
fun break_point _ = NONE;

end;