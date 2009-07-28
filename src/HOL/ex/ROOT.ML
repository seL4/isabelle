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
  "../NumberTheory/Factorization",
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
  "Arithmetic_Series_Complex",
  "HarmonicSeries",
  "Refute_Examples",
  "Quickcheck_Examples",
  "Landau"
];

(setmp_noncritical proofs 2 (setmp_noncritical Multithreading.max_threads 1 use_thy))
  "Hilbert_Classical";


use_thy "SVC_Oracle";

fun svc_enabled () = getenv "SVC_HOME" <> "";
fun if_svc_enabled f x = if svc_enabled () then f x else ();

if_svc_enabled use_thy "svc_test";


(* requires a proof-generating SAT solver (zChaff or MiniSAT) to be *)
(* installed:                                                       *)
try use_thy "SAT_Examples";
Future.shutdown ();

(* requires zChaff (or some other reasonably fast SAT solver) to be *)
(* installed:                                                       *)
if getenv "ZCHAFF_HOME" <> "" then
  use_thy "Sudoku"
else ();

HTML.with_charset "utf-8" (no_document use_thys)
  ["Hebrew", "Chinese", "Serbian"];
