(*  Title:      HOL/ex/ROOT.ML
    ID:         $Id$

Miscellaneous examples for Higher-Order Logic.
*)

no_document use_thys [
  "Parity",
  "Code_Eval",
  "State_Monad",
  "Efficient_Nat_examples",
  "ExecutableContent",
  "FuncSet",
  "Word",
  "Eval_Examples",
  "Quickcheck",
  "Term_Of_Syntax"
];

no_document use_thy "Codegenerator";
(*no_document use_thy "Codegenerator_Pretty";*)

use_thys [
  "Numeral",
  "ImperativeQuicksort",
  "Higher_Order_Logic",
  "Abstract_NAT",
  "Guess",
  "Binary",
  "Recdefs",
  "Fundefs",
  "Induction_Scheme",
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
  "MergeSort",
  "Lagrange",
  "Groebner_Examples",
  "MT",
  "Unification",
  "Commutative_RingEx",
  "Commutative_Ring_Complete",
  "Primrec",
  "Tarski",
  "Adder",
  "Classical",
  "set",
  "Meson_Test",
  "Code_Antiq",
  "LexOrds",
  "Coherent"
];

setmp Proofterm.proofs 2 time_use_thy "Hilbert_Classical";

time_use_thy "Dense_Linear_Order_Ex";
time_use_thy "PresburgerEx";
time_use_thy "Reflected_Presburger";

time_use_thy "Reflection";

time_use_thy "SVC_Oracle";

(*check if user has SVC installed*)
fun svc_enabled () = getenv "SVC_HOME" <> "";
fun if_svc_enabled f x = if svc_enabled () then f x else ();

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

HTML.with_charset "utf-8" (no_document use_thys) ["Hebrew", "Chinese"];

no_document use_thys [
  "../NumberTheory/Factorization",
  "../Library/BigO"
];

use_thys [
  "../Complex/ex/BinEx",
  "../Complex/ex/Sqrt",
  "../Complex/ex/Sqrt_Script",
  "../Complex/ex/BigO_Complex",

  "../Complex/ex/Arithmetic_Series_Complex",
  "../Complex/ex/HarmonicSeries",

  "../Complex/ex/MIR",
  "../Complex/ex/ReflectedFerrack"
];

