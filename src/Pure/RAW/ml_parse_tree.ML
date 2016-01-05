(*  Title:      Pure/RAW/ml_parse_tree.ML
    Author:     Makarius

Additional ML parse tree components for Poly/ML.
*)

signature ML_PARSE_TREE =
sig
  val completions: PolyML.ptProperties -> string list option
  val breakpoint: PolyML.ptProperties -> bool Unsynchronized.ref option
end;

structure ML_Parse_Tree: ML_PARSE_TREE =
struct

fun completions _ = NONE;
fun breakpoint _ = NONE;

end;