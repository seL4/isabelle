(*  Title:      HOL/Extraction/ROOT.ML
    ID:         $Id$

Examples for program extraction in Higher-Order Logic.
*)

if HOL_proofs < 2 then
  warning "HOL proof terms required for running extraction examples"
else
  (Proofterm.proofs := 2;
   no_document time_use_thy "Efficient_Nat";
   use_thys ["QuotRem", "Warshall", "Higman", "Pigeonhole"]);
