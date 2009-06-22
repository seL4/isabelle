(*  Title:      HOL/Isar_examples/ROOT.ML
    Author:     Markus Wenzel, TU Muenchen

Miscellaneous Isabelle/Isar examples for Higher-Order Logic.
*)

no_document use_thys ["../NumberTheory/Primes", "../NumberTheory/Fibonacci"];

use_thys [
  "Basic_Logic",
  "Cantor",
  "Peirce",
  "Drinker",
  "Expr_Compiler",
  "Group",
  "Summation",
  "Knaster_Tarski",
  "Mutilated_Checkerboard",
  "Puzzle",
  "Nested_Datatype",
  "Hoare_Ex"
];
