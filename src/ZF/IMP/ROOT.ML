(*  Title:      ZF/IMP/ROOT.ML
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM

Executes the formalization of the denotational and operational semantics of a
simple while-language, including an equivalence proof. The whole development
essentially formalizes/transcribes chapters 2 and 5 of

Glynn Winskel. The Formal Semantics of Programming Languages.
MIT Press, 1993.

*)

ZF_build_completed;     (*Make examples fail if ZF did*)

writeln"Root file for ZF/IMP";
set proof_timing;

time_use_thy "Equiv";
