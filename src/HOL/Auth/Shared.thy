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
        (*Server knows all long-term keys; other agents know only their own*)
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
  sees_Nil  "sees lost A []       = initState lost A"
  sees_Cons "sees lost A (ev#evs) = sees1 A ev Un sees lost A evs"


(*Agents generate random (symmetric) keys and nonces.
  The numeric argument is typically the length of the current trace.
  An injective pairing function allows multiple keys/nonces to be generated
	in one protocol round.  A typical candidate for npair(i,j) is
	2^j(2i+1)
*)

consts
  nPair :: "nat*nat => nat"
  newN  :: "nat => nat"
  newK  :: "nat => key"

rules
  inj_shrK        "inj shrK"
  inj_nPair       "inj nPair"
  inj_newN        "inj newN"
  inj_newK        "inj newK"

  newK_neq_shrK   "newK i ~= shrK A" 
  isSym_newK      "isSymKey (newK i)"

end
