(*  Title:      HOL/Extraction/ROOT.ML
    ID:         $Id$

Examples for program extraction in Higher-Order Logic.
*)

if HOL_proofs < 2 then
  warning "HOL proof terms required for running extraction examples"
else
  (proofs := 2;
   time_use_thy "QuotRem";
   time_use_thy "Warshall";
   time_use_thy "Higman");
