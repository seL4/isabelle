(*  Title:      HOL/ex/ROOT.ML

Miscellaneous examples for Higher-Order Logic.
*)

no_document use_thys [
  "State_Monad",
  "Efficient_Nat_examples",
  "FuncSet",
  "Word",
  "Eval_Examples",
  "Codegenerator_Test",
  "Codegenerator_Pretty_Test",
  "NormalForm",
  "Predicate_Compile",
  "Predicate_Compile_ex"
];

use_thys [
  "Numeral",
  "Higher_Order_Logic",
  "Abstract_NAT",
  "Guess",
  "Binary",
  "Recdefs",
  "Fundefs",
  "Induction_Scheme",
  "InductiveInvariant_examples",
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
  "Termination",
  "Coherent",
  "PresburgerEx",
  "ReflectionEx",
  "BinEx",
  "Sqrt",
  "Sqrt_Script",
  "Transfer_Ex",
  "Arithmetic_Series_Complex",
  "HarmonicSeries",
  "Refute_Examples",
  "Quickcheck_Examples",
  "Landau"
];

Future.shutdown ();
(setmp_noncritical proofs 2 (setmp_noncritical Multithreading.max_threads 1 use_thy))
  "Hilbert_Classical";

use_thy "SVC_Oracle";
if getenv "SVC_HOME" = "" then ()
else use_thy "svc_test";

(*requires a proof-generating SAT solver (zChaff or MiniSAT)*)
try use_thy "SAT_Examples";

(*requires zChaff (or some other reasonably fast SAT solver)*)
if getenv "ZCHAFF_HOME" = "" then ()
else use_thy "Sudoku";

HTML.with_charset "utf-8" (no_document use_thys)
  ["Hebrew", "Chinese", "Serbian"];
