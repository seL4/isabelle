(*  Title:      HOL/TPTP/ROOT.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Nik Sultana, University of Cambridge
    Copyright   2011

TPTP-related extensions.
*)

use_thys [
  "ATP_Theory_Export",
  "MaSh_Export",
  "MaSh_Import",
  "TPTP_Interpret",
  "THF_Arith"
];

Unsynchronized.setmp Proofterm.proofs (!Proofterm.proofs)
  use_thy "ATP_Problem_Import";
