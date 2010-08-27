quick_and_dirty := true;
Thy_Output.source_default := true;
use "../../antiquote_setup.ML";

use_thys [
  "Introduction",
  "Framework",
  "First_Order_Logic",
  "Outer_Syntax",
  "Document_Preparation",
  "Spec",
  "Proof",
  "Inner_Syntax",
  "Misc",
  "Generic",
  "HOL_Specific",
  "Quick_Reference",
  "Symbols",
  "ML_Tactic"
];
