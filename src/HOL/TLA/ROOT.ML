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

reset global_names;

(*FIXME: the old auto_tac is sometimes needed!*)
fun old_auto_tac (cs,ss) = 
    let val cs' = cs addss ss 
    in  EVERY [TRY (safe_tac cs'),
               REPEAT (FIRSTGOAL (fast_tac cs')),
               TRY (safe_tac (cs addSss ss)),
               prune_params_tac] 
    end;


use_thy "TLA";

val TLA_build_completed = ();
