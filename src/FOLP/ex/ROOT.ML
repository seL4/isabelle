(*  Title:      FOLP/ex/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Examples for First-Order Logic. 
*)

use_thys [
  "Intro",
  "Nat",
  "Foundation",
  "If"
];

writeln"\n** Intuitionistic examples **\n";
time_use     "int.ML";

val thy = theory "IFOLP"  and  tac = IntPr.fast_tac 1;
time_use     "prop.ML";
time_use     "quant.ML";

writeln"\n** Classical examples **\n";
time_use     "cla.ML";

val thy = theory "FOLP"  and  tac = Cla.fast_tac FOLP_cs 1;
time_use     "prop.ML";
time_use     "quant.ML";
