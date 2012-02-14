(*  Title:      HOL/ex/ROOT.ML

Miscellaneous examples for Higher-Order Logic.
*)

no_document use_thys [
  "~~/src/HOL/Library/State_Monad",
  "Efficient_Nat_examples",
  "~~/src/HOL/Library/FuncSet",
  "Eval_Examples",
  "Normalization_by_Evaluation",
  "Hebrew",
  "Chinese",
  "Serbian"
];

use_thys [
  "Iff_Oracle",
  "Coercion_Examples",
  "Numeral",
  "Higher_Order_Logic",
  "Abstract_NAT",
  "Guess",
  "Binary",
  "Fundefs",
  "Induction_Schema",
  "LocaleTest2",
  "Records",
  "While_Combinator_Example",
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
  "Tree23",
  "MergeSort",
  "Lagrange",
  "Groebner_Examples",
  "MT",
  "Unification",
  "Primrec",
  "Tarski",
  "Classical",
  "Set_Theory",
  "Meson_Test",
  "Termination",
  "Coherent",
  "PresburgerEx",
  "ReflectionEx",
  "Sqrt",
  "Sqrt_Script",
  "Transfer_Ex",
  "Arithmetic_Series_Complex",
  "HarmonicSeries",
  "Refute_Examples",
  "Quickcheck_Examples",
  "Quickcheck_Lattice_Examples",
  "Landau",
  "Execute_Choice",
  "Summation",
  "Gauge_Integration",
  "Dedekind_Real",
  "Quicksort",
  "Birthday_Paradox",
  "List_to_Set_Comprehension_Examples",
  "Set_Algebras",
  "Seq",
  "Simproc_Tests",
  "Executable_Relation"
];

if getenv "ISABELLE_GHC" = "" then ()
else use_thy "Quickcheck_Narrowing_Examples";

use_thy "SVC_Oracle";
if getenv "SVC_HOME" = "" then ()
else use_thy "svc_test";

(*requires zChaff (or some other reasonably fast SAT solver)*)
if getenv "ZCHAFF_HOME" = "" then ()
else use_thy "Sudoku";

(*requires a proof-generating SAT solver (zChaff or MiniSAT)*)
(*global side-effects ahead!*)
try use_thy "SAT_Examples";   (* FIXME try!? (not really a proper test) *)
