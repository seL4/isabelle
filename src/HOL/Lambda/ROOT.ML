(*  Title:      HOL/Lambda/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

Syntax.ambiguity_level := 100;
proofs := 2;

use_thy "Eta";
no_document use_thy "Accessible_Part";
use_thy "StrongNorm";
if HOL_proofs < 2 then
  warning "HOL proof terms required for running theory WeakNorm"
else use_thy "WeakNorm";
