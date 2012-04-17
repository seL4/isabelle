(*  Title:      HOL/TPTP/ROOT.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Nik Sultana, University of Cambridge
    Copyright   2011

TPTP-related extensions.
*)

use_thys [
  "ATP_Theory_Export",
  "TPTP_Interpret"
];

Unsynchronized.setmp Proofterm.proofs (!Proofterm.proofs)
  use_thys [
    "ATP_Problem_Import",
    "CASC_Setup"
  ];
