(*  Title:      HOL/ex/ROOT.ML
    ID:         $Id$

Miscellaneous examples for Higher-Order Logic.
*)

time_use_thy "Recdefs";
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
time_use     "cla.ML";
time_use     "mesontest.ML";
time_use_thy "mesontest2";
time_use_thy "BT";
time_use_thy "AVL";
time_use_thy "InSort";
time_use_thy "Qsort";
time_use_thy "Puzzle";

time_use_thy "IntRing";

time_use_thy "set";
time_use_thy "MT";
time_use_thy "Tarski";

if_svc_enabled time_use_thy "svc_test";
