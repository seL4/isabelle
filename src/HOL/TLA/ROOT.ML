(*  Title:      TLA/ROOT.ML

Adds the Temporal Logic of Actions to a database containing Isabelle/HOL.
*)

val banner = "Temporal Logic of Actions";

(*
   raise the ambiguity level to avoid ambiguity warnings;
   since Trueprop and TrueInt have both empty syntax, there is
   an unavoidable ambiguity in the TLA (actually, Intensional) grammar.
*)
Syntax.ambiguity_level := 10000;

use_thy "TLA";

val TLA_build_completed = ();
