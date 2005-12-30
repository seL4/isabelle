(*  Title:      Provers/make_elim.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Classical version of Tactic.make_elim

In classical logic, we can make stronger elimination rules using this version.
For instance, the HOL rule injD is transformed into
    [| inj ?f; ~ ?W ==> ?f ?x = ?f ?y; ?x = ?y ==> ?W |] ==> ?W
while Tactic.make_elim would yield the weaker rule
    [| inj ?f; ?f ?x = ?f ?y; ?x = ?y ==> PROP ?W |] ==> PROP ?W
Such rules can cause Fast_tac to fail and Blast_tac to report "PROOF FAILED"
*)

signature MAKE_ELIM_DATA =
sig
  val cla_dist_concl: thm  (*"[| ~Z ==> PROP X; PROP Y ==> Z;  PROP X ==> PROP Y |] ==> Z"*)
end;

functor Make_Elim_Fun(Data: MAKE_ELIM_DATA)  =
struct

fun make_elim rl =
  let
    fun compose_extra nsubgoal (tha,i,thb) =
      Seq.list_of (bicompose false (false,tha,nsubgoal) i thb)
    val revcut_rl' = Drule.incr_indexes rl revcut_rl

    fun making (i,rl) =
      case compose_extra 2 (Data.cla_dist_concl,i,rl) of
        [] => rl     (*terminates by clash of variables!*)
      | rl'::_ => making (i+1,rl')
    in  making (2, hd (compose_extra 1 (rl, 1, revcut_rl')))  end
    handle (*in default, use the previous version, which never fails*)
      THM _ => Tactic.make_elim rl | Empty => Tactic.make_elim rl;

end;
