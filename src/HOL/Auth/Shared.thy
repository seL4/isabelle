(*  Title:      HOL/Auth/Shared
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Shared Keys (common to all symmetric-key protocols)

Shared, long-term keys; initial states of agents
*)

theory Shared = Event
files ("Shared_lemmas.ML"):

consts
  shrK    :: "agent => key"  (*symmetric keys*)

axioms
  isSym_keys: "isSymKey K"	(*All keys are symmetric*)
  inj_shrK:   "inj shrK"	(*No two agents have the same long-term key*)

primrec
        (*Server knows all long-term keys; other agents know only their own*)
  initState_Server:  "initState Server     = Key ` range shrK"
  initState_Friend:  "initState (Friend i) = {Key (shrK (Friend i))}"
  initState_Spy:     "initState Spy        = Key`shrK`bad"


axioms
  (*Unlike the corresponding property of nonces, this cannot be proved.
    We have infinitely many agents and there is nothing to stop their
    long-term keys from exhausting all the natural numbers.  The axiom
    assumes that their keys are dispersed so as to leave room for infinitely
    many fresh session keys.  We could, alternatively, restrict agents to
    an unspecified finite number.*)
  Key_supply_ax:  "finite KK ==> EX K. K ~: KK & Key K ~: used evs"

use "Shared_lemmas.ML"

(*Lets blast_tac perform this step without needing the simplifier*)
lemma invKey_shrK_iff [iff]:
     "(Key (invKey K) \\<in> X) = (Key K \\<in> X)"
by auto;

(*Specialized methods*)

method_setup analz_freshK = {*
    Method.no_args
     (Method.METHOD
      (fn facts => EVERY [REPEAT_FIRST (resolve_tac [allI, impI]),
                          REPEAT_FIRST (rtac analz_image_freshK_lemma),
                          ALLGOALS (asm_simp_tac analz_image_freshK_ss)])) *}
    "for proving the Session Key Compromise theorem"

method_setup possibility = {*
    Method.no_args (Method.METHOD (fn facts => possibility_tac)) *}
    "for proving possibility theorems"

end
