(*  Title:      Pure/ML/ml_parse_tree_polyml-5.5.3.ML
    Author:     Makarius

Additional ML parse tree components for Poly/ML 5.5.3, or later.
*)

structure ML_Parse_Tree: ML_PARSE_TREE =
struct

fun completions (PolyML.PTcompletions x) = SOME x
  | completions _ = NONE;

fun breakpoint (PolyML.PTbreakPoint x) = SOME x
  | breakpoint _ = NONE;

end;