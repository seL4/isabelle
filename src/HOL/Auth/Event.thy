(*  Title:      HOL/Auth/Event
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of events for security protocols

Datatype of events; function "spies"; freshness

"bad" agents have been broken by the Spy; their private keys and internal
    stores are visible to him
*)

theory Event = Message
files ("Event_lemmas.ML"):

consts  (*Initial states of agents -- parameter of the construction*)
  initState :: "agent => msg set"

datatype
  event = Says  agent agent msg
        | Gets  agent       msg
        | Notes agent       msg
       
consts 
  bad    :: "agent set"				(*compromised agents*)
  knows  :: "agent => event list => msg set"


(*"spies" is retained for compatibility's sake*)
syntax
  spies  :: "event list => msg set"

translations
  "spies"   => "knows Spy"


axioms
  (*Spy has access to his own key for spoof messages, but Server is secure*)
  Spy_in_bad     [iff] :    "Spy \\<in> bad"
  Server_not_bad [iff] : "Server \\<notin> bad"

primrec
  knows_Nil:   "knows A [] = initState A"
  knows_Cons:
    "knows A (ev # evs) =
       (if A = Spy then 
	(case ev of
	   Says A' B X => insert X (knows Spy evs)
	 | Gets A' X => knows Spy evs
	 | Notes A' X  => 
	     if A' \\<in> bad then insert X (knows Spy evs) else knows Spy evs)
	else
	(case ev of
	   Says A' B X => 
	     if A'=A then insert X (knows A evs) else knows A evs
	 | Gets A' X    => 
	     if A'=A then insert X (knows A evs) else knows A evs
	 | Notes A' X    => 
	     if A'=A then insert X (knows A evs) else knows A evs))"

(*
  Case A=Spy on the Gets event
  enforces the fact that if a message is received then it must have been sent,
  therefore the oops case must use Notes
*)

consts
  (*Set of items that might be visible to somebody:
    complement of the set of fresh items*)
  used :: "event list => msg set"

primrec
  used_Nil:   "used []         = (UN B. parts (initState B))"
  used_Cons:  "used (ev # evs) =
		     (case ev of
			Says A B X => parts {X} Un (used evs)
		      | Gets A X   => used evs
		      | Notes A X  => parts {X} Un (used evs))"


use "Event_lemmas.ML"

method_setup analz_mono_contra = {*
    Method.no_args
      (Method.METHOD (fn facts => REPEAT_FIRST analz_mono_contra_tac)) *}
    "for proving theorems of the form X \\<notin> analz (knows Spy evs) --> P"

end
