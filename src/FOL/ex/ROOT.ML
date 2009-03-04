(*  Title:      FOL/ex/ROOT.ML

Examples for First-Order Logic. 
*)

use_thys [
  "First_Order_Logic",
  "Natural_Numbers",
  "Intro",
  "Nat",
  "Nat_Class",
  "Foundation",
  "Prolog",
  "Intuitionistic",
  "Propositional_Int",
  "Quantifiers_Int",
  "Classical",
  "Propositional_Cla",
  "Quantifiers_Cla",
  "Miniscope",
  "If",
  "Iff_Oracle"
];

(*regression test for locales -- sets several global flags!*)
no_document use_thy "LocaleTest";
