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


(*Agents generate "random" numbers for use as symmetric keys, as well as
  nonces.*)

consts
  random :: "nat*nat => nat"

constdefs
  newN   :: event list => nat
  "newN evs == random (length evs, 0)"

  newK   :: event list => nat
  "newK evs == random (length evs, 1)"

rules
  inj_shrK        "inj shrK"
  inj_random      "inj random"

  random_neq_shrK "random ij ~= shrK A" 
  isSym_random    "isSymKey (random ij)"

end
