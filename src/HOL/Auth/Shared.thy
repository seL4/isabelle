(*  Title:      HOL/Auth/Shared
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Shared Keys (common to all symmetric-key protocols)

Server keys; initial states of agents; new nonces and keys; function "sees" 
*)

Shared = Message + List + 

consts
  shrK    :: agent => key  (*symmetric keys*)

rules
  isSym_shrK "isSymKey (shrK A)"

consts  (*Initial states of agents -- parameter of the construction*)
  initState :: [agent set, agent] => msg set

primrec initState agent
        (*Server knows all keys; other agents know only their own*)
  initState_Server  "initState lost Server     = Key `` range shrK"
  initState_Friend  "initState lost (Friend i) = {Key (shrK (Friend i))}"
  initState_Spy     "initState lost Spy        = Key``shrK``lost"


datatype  (*Messages, and components of agent stores*)
  event = Says agent agent msg

consts  
  sees1 :: [agent, event] => msg set

primrec sees1 event
           (*Spy reads all traffic whether addressed to him or not*)
  sees1_Says  "sees1 A (Says A' B X)  = (if A:{B,Spy} then {X} else {})"

consts  
  sees :: [agent set, agent, event list] => msg set

primrec sees list
        (*Initial knowledge includes all public keys and own private key*)
  sees_Nil  "sees lost A []       = initState lost A"
  sees_Cons "sees lost A (ev#evs) = sees1 A ev Un sees lost A evs"


(*Agents generate "random" nonces.  Different traces always yield
  different nonces.  Same applies for keys.*)
consts
  newN :: "event list => nat"
  newK :: "event list => key"

rules
  inj_shrK      "inj shrK"

  newN_length   "(newN evs = newN evt) ==> (length evs = length evt)"
  newK_length   "(newK evs = newK evt) ==> (length evs = length evt)"

  newK_neq_shrK "newK evs ~= shrK A" 
  isSym_newK    "isSymKey (newK evs)"

end
