(*  Title:      HOL/Auth/Event
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of events for security protocols

Datatype of events; function "spies"; freshness

"bad" agents have been broken by the Spy; their private keys and internal
    stores are visible to him
*)

Event = Message + List + 

consts  (*Initial states of agents -- parameter of the construction*)
  initState :: agent => msg set

datatype  (*Messages--could add another constructor for agent knowledge*)
  event = Says  agent agent msg
        | Notes agent       msg

consts  
  bad    :: agent set        (*compromised agents*)
  spies  :: event list => msg set

rules
  (*Spy has access to his own key for spoof messages, but Server is secure*)
  Spy_in_bad     "Spy: bad"
  Server_not_bad "Server ~: bad"

primrec spies list
           (*Spy reads all traffic whether addressed to him or not*)
  spies_Nil   "spies []       = initState Spy"
  spies_Cons  "spies (ev # evs) =
	         (case ev of
		    Says A B X => insert X (spies evs)
		  | Notes A X  => 
	              if A:bad then insert X (spies evs) else spies evs)"

consts
  (*Set of items that might be visible to somebody:
    complement of the set of fresh items*)
  used :: event list => msg set

primrec used list
  used_Nil   "used []         = (UN B. parts (initState B))"
  used_Cons  "used (ev # evs) =
	         (case ev of
		    Says A B X => parts {X} Un (used evs)
		  | Notes A X  => parts {X} Un (used evs))"

end
