(*  Title:      HOL/ex/ROOT.ML
    ID:         $Id$

Miscellaneous examples for Higher-Order Logic.
*)

no_document use_thy "Parity";
no_document use_thy "GCD";

no_document time_use_thy "Classpackage";
no_document time_use_thy "Eval_examples";
no_document time_use_thy "Random";
no_document time_use_thy "Codegenerator_Rat";
no_document time_use_thy "Codegenerator";

time_use_thy "Higher_Order_Logic";
time_use_thy "Abstract_NAT";
time_use_thy "Guess";
time_use_thy "Binary";

time_use_thy "Recdefs";
time_use_thy "Fundefs";
time_use_thy "InductiveInvariant_examples";
time_use_thy "Primrec";
time_use_thy "Locales";
time_use_thy "LocaleTest2";
time_use_thy "Records";
time_use_thy "MonoidGroup";
time_use_thy "BinEx";
time_use_thy "Hex_Bin_Examples";
setmp proofs 2 time_use_thy "Hilbert_Classical";
time_use_thy "Antiquote";
time_use_thy "Multiquote";

time_use_thy "PER";
time_use_thy "NatSum";
time_use_thy "ThreeDivides";
time_use_thy "Intuitionistic";
time_use_thy "Classical";
time_use_thy "CTL";
time_use_thy "mesontest2";
time_use_thy "PresburgerEx";
time_use_thy "Reflected_Presburger";
time_use_thy "BT";
time_use_thy "InSort";
time_use_thy "Qsort";
time_use_thy "MergeSort";
time_use_thy "Puzzle";

time_use_thy "Lagrange";
time_use_thy "Commutative_RingEx";
time_use_thy "Commutative_Ring_Complete";
time_use_thy "Reflection";

time_use_thy "set";
time_use_thy "MT";

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

time_use_thy "Unification";
