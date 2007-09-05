(*  Title:      HOL/ex/ROOT.ML
    ID:         $Id$

Miscellaneous examples for Higher-Order Logic.
*)

no_document use_thys [
  "Parity",
  "GCD"
];

use_thys [
  "Higher_Order_Logic",
  "Abstract_NAT",
  "Guess",
  "Binary",
  "Recdefs",
  "Fundefs",
  "InductiveInvariant_examples",
  "Locales",
  "LocaleTest2",
  "Records",
  "MonoidGroup",
  "BinEx",
  "Hex_Bin_Examples",
  "Antiquote",
  "Multiquote",
  "PER",
  "NatSum",
  "ThreeDivides",
  "Intuitionistic",
  "CTL",
  "Arith_Examples",
  "BT",
  "InSort",
  "Qsort",
  "MergeSort",
  "Puzzle",
  "Lagrange",
  "Groebner_Examples",
  "MT",
  "Unification",
  "Commutative_RingEx",
  "Commutative_Ring_Complete"
];

no_document time_use_thy "Classpackage";

no_document time_use_thy "Eval";
time_use_thy "Eval_Examples";

no_document time_use_thy "State_Monad";
no_document time_use_thy "Pretty_Int";
time_use_thy "Random";

no_document time_use_thy "Executable_Rat";
no_document time_use_thy "Efficient_Nat";
no_document time_use_thy "Codegenerator";
no_document time_use_thy "Codegenerator_Pretty";


setmp proofs 2 time_use_thy "Hilbert_Classical";

time_use_thy "Primrec";
time_use_thy "Classical";
time_use_thy "set";

time_use_thy "Meson_Test";
time_use_thy "Dense_Linear_Order_Ex";
time_use_thy "PresburgerEx";
time_use_thy "Reflected_Presburger";

time_use_thy "Reflection";

time_use_thy "NBE";

no_document use_thy "FuncSet";
time_use_thy "Tarski";

time_use_thy "SVC_Oracle";
if_svc_enabled time_use_thy "svc_test";

(* requires a proof-generating SAT solver (zChaff or MiniSAT) to be *)
(* installed:                                                       *)
try time_use_thy "SAT_Examples";

(* requires zChaff (or some other reasonably fast SAT solver) to be *)
(* installed:                                                       *)
if getenv "ZCHAFF_HOME" <> "" then
  time_use_thy "Sudoku"
else ();

time_use_thy "Refute_Examples";
time_use_thy "Quickcheck_Examples";
no_document time_use_thy "NormalForm";

no_document use_thy "Word";
time_use_thy "Adder";

HTML.with_charset "utf-8" (no_document time_use_thy) "Hebrew";
HTML.with_charset "utf-8" (no_document time_use_thy) "Chinese";
