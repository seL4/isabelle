(*  Title:      FOL/ex/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Examples for First-Order Logic. 
*)

use_thys [
  "First_Order_Logic",
  "Natural_Numbers",
  "Intro",
  "Nat",
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

  "NatClass",
  "IffOracle"
];

(*regression test for locales -- sets several global flags!*)
no_document use_thy "NewLocaleTest";

