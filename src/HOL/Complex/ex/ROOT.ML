(*  Title:      HOL/Complex/ex/ROOT.ML
    ID:         $Id$

Miscellaneous examples.
*)

no_document use_thys [
  "../../NumberTheory/Factorization",
  "BigO",
  "NatPair"
];

use_thys [
  "BinEx",
  "Sqrt",
  "Sqrt_Script",
  "NSPrimes",
  "BigO_Complex",

  "Arithmetic_Series_Complex",
  "HarmonicSeries",

  "DenumRat"
];

if String.isPrefix "smlnj" ml_system then ()  (* FIXME tmp *)
else use_thys ["MIR", "ReflectedFerrack"];

