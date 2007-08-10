(*  Title:      HOL/Isar_examples/ROOT.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Miscellaneous Isabelle/Isar examples for Higher-Order Logic.
*)

no_document use_thys ["../NumberTheory/Primes", "../NumberTheory/Fibonacci"];

use_thys [
  "BasicLogic",
  "Cantor",
  "Peirce",
  "Drinker",
  "ExprCompiler",
  "Group",
  "Summation",
  "KnasterTarski",
  "MutilatedCheckerboard",
  "Puzzle",
  "NestedDatatype",
  "HoareEx"
];
