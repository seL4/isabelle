(*  Title: 	CHOL/IMP/ROOT.ML
    ID:         $Id$
    Author: 	Heiko Loetzbeyer, Robert Sandner, Tobias Nipkow
    Copyright   1995 TUM

The formalization of the denotational, operational and axiomatic semantics of
a simple while-language, including
(1) an equivalence proof between denotational and operational semantics and
(2) the derivation of the Hoare rules from the denotational semantics.
The whole development essentially formalizes/transcribes chapters 2, 5 and 6 of

Glynn Winskel. The Formal Semantics of Programming Languages.
MIT Press, 1993.

*)

CHOL_build_completed;	(*Make examples fail if CHOL did*)

writeln"Root file for CHOL/IMP";
proof_timing := true;
loadpath := [".","IMP"];
(time_use_thy "Properties";
 time_use_thy "Equiv";
 time_use_thy "Hoare"
) handle _ => exit 1;
