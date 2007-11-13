(*  Title:      HOL/Extraction/ROOT.ML
    ID:         $Id$

Examples for program extraction in Higher-Order Logic.
*)

if HOL_proofs < 2 then
  warning "HOL proof terms required for running extraction examples"
else
  (Proofterm.proofs := 2;
   no_document use_thys ["Efficient_Nat", "~~/src/HOL/NumberTheory/Factorization"];
   use_thys ["Greatest_Common_Divisor", "Warshall", "Higman", "Pigeonhole", "Euclid"]);
