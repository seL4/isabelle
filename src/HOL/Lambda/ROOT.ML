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
time_use_thy "WeakNorm";
