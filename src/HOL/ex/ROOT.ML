(*  Title:      HOL/ex/ROOT.ML
    ID:         $Id$

Miscellaneous examples for Higher-Order Logic.
*)

(*some examples of recursive function definitions: the TFL package*)
time_use_thy "Recdefs";
time_use_thy "Primrec";

time_use_thy "NatSum";
time_use     "cla.ML";
time_use     "mesontest.ML";
time_use     "mesontest2.ML";
time_use_thy "BT";
time_use_thy "AVL";
time_use_thy "InSort";
time_use_thy "Qsort";
time_use_thy "Puzzle";

time_use_thy "IntRing";

time_use_thy "set";
time_use_thy "MT";
time_use_thy "Tarski";

time_use_thy "StringEx";
time_use_thy "BinEx";

if_svc_enabled time_use_thy "svc_test";

(*basic use of extensible records*)
time_use_thy "MonoidGroup";
time_use_thy "Points";

(*groups via locales*)
time_use_thy "PiSets";
time_use_thy "LocaleGroup";

(*advanced concrete syntax*)
time_use_thy "Tuple";
time_use_thy "Antiquote";
time_use_thy "Multiquote";
