(*  Title:      HOL/Lambda/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

Syntax.ambiguity_level := 100;
proofs := 2;
IsarOutput.modes := "no_brackets" :: !IsarOutput.modes;

set timing;
time_use_thy "Eta";
no_document time_use_thy "Accessible_Part";
time_use_thy "StrongNorm";
if HOL_proofs < 2 then
  warning "HOL proof terms required for running theory WeakNorm"
else time_use_thy "WeakNorm";
