(*  Title:      HOL/ex/ROOT.ML
    ID:         $Id$

Miscellaneous examples for Higher-Order Logic.
*)

time_use_thy "Higher_Order_Logic";

time_use_thy "Recdefs";
time_use_thy "InductiveInvariant_examples";
time_use_thy "Primrec";
time_use_thy "Locales";
time_use_thy "Records";
time_use_thy "MonoidGroup";
time_use_thy "StringEx";
time_use_thy "BinEx";
setmp proofs 2 time_use_thy "Hilbert_Classical";
time_use_thy "Antiquote";
time_use_thy "Multiquote";
time_use_thy "Tuple";

time_use_thy "NatSum";
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

time_use_thy "set";
time_use_thy "MT";

no_document use_thy "FuncSet";
time_use_thy "Tarski";

time_use_thy "SVC_Oracle";
if_svc_enabled time_use_thy "svc_test";

(* requires zChaff with proof generation to be installed: *)
time_use_thy "SAT_Examples" handle ERROR => ();

time_use_thy "Refute_Examples";
time_use_thy "Quickcheck_Examples";

no_document use_thy "Word";
time_use_thy "Adder";

HTML.with_charset "utf-8" (no_document time_use_thy) "Hebrew";
HTML.with_charset "utf-8" (no_document time_use_thy) "Chinese";
