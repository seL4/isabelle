(*  Title:      HOL/Auth/Event
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of events for security protocols

Datatype of events; function "sees"; freshness
*)

Event = Message + List + 

consts  (*Initial states of agents -- parameter of the construction*)
  initState :: [agent set, agent] => msg set

datatype  (*Messages--could add another constructor for agent knowledge*)
  event = Says  agent agent msg
        | Notes agent       msg

consts  
  sees1 :: [agent, event] => msg set

primrec sees1 event
           (*Spy reads all traffic whether addressed to him or not*)
  sees1_Says  "sees1 A (Says A' B X)  = (if A:{B,Spy} then {X} else {})"
  sees1_Notes "sees1 A (Notes A' X)   = (if A = A'    then {X} else {})"

consts  
  sees :: [agent set, agent, event list] => msg set

primrec sees list
  sees_Nil  "sees lost A []       = initState lost A"
  sees_Cons "sees lost A (ev#evs) = sees1 A ev Un sees lost A evs"


constdefs
  (*Set of items that might be visible to somebody: complement of the set
        of fresh items*)
  used :: event list => msg set
    "used evs == parts (UN lost B. sees lost B evs)"

end
