(*  Title:      HOL/Isar_examples/ROOT.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Miscellaneous Isabelle/Isar examples for Higher-Order Logic.
*)

time_use_thy "BasicLogic";
time_use_thy "Cantor";
time_use_thy "Peirce";
time_use_thy "ExprCompiler";
time_use_thy "Group";
time_use_thy "Summation";
time_use_thy "KnasterTarski";
time_use_thy "MutilatedCheckerboard";
with_path "../Induct"       time_use_thy "MultisetOrder";
with_path "../W0"           time_use_thy "W_correct";
with_path "../NumberTheory" time_use_thy "Fibonacci";
time_use_thy "Puzzle";
time_use_thy "NestedDatatype";
