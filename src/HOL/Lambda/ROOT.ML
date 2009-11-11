(*  Title:      HOL/Lambda/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

Syntax.ambiguity_level := 100;
Proofterm.proofs := 2;

no_document use_thys ["Code_Integer"];
use_thys ["Eta", "StrongNorm", "Standardization"];
if HOL_proofs < 2 then
  warning "HOL proof terms required for running theory WeakNorm"
else use_thys ["WeakNorm"];
